"""Small Go parser for the Python Go-runtime translation layer.

This parser intentionally stops at a language AST.  It does not compile Go and
it does not pretend to implement the Go compiler's type checker.  The AST keeps
constructs that the companion runtime modules can lower later: interfaces,
switch/case, goto/labels, goroutines, defer, channels and ordinary declarations.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, List, Optional, Sequence, Tuple
import re


# ----------------------------- lexer ---------------------------------------

KEYWORDS = {
    "break", "default", "func", "interface", "select", "case", "defer",
    "go", "map", "struct", "chan", "else", "goto", "package", "switch",
    "const", "fallthrough", "if", "range", "type", "continue", "for",
    "import", "return", "var",
}

MULTI_OPS = sorted([
    "...", ">>=", "<<=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=",
    "&^=", "==", "!=", "<=", ">=", "&&", "||", "++", "--", ":=", "<-",
    "<<", ">>", "&^", "=>",
], key=len, reverse=True)

SINGLE = set("+-*/%&|^<>=!~()[]{}.,;:~")


@dataclass(frozen=True)
class Token:
    kind: str
    value: str
    line: int
    column: int

    def __repr__(self):
        return f"Token({self.kind!r}, {self.value!r}, {self.line}:{self.column})"


class GoSyntaxError(SyntaxError):
    pass


class Lexer:
    def __init__(self, source: str):
        self.source = source
        self.i = 0
        self.line = 1
        self.col = 1
        self.tokens: List[Token] = []
        self._line_start = True

    def _advance(self, text: str) -> None:
        n = text.count("\n")
        if n:
            self.line += n
            self.col = len(text.rsplit("\n", 1)[-1]) + 1
            self._line_start = True
        else:
            self.col += len(text)
            self._line_start = False
        self.i += len(text)

    def _emit(self, kind: str, value: str, line: int, col: int) -> None:
        self.tokens.append(Token(kind, value, line, col))

    def tokenize(self) -> List[Token]:
        s = self.source
        while self.i < len(s):
            c = s[self.i]
            if c in " \t\r":
                j = self.i + 1
                while j < len(s) and s[j] in " \t\r": j += 1
                self._advance(s[self.i:j]); continue
            if c == "\n":
                self._advance("\n"); continue
            if s.startswith("//", self.i):
                j = s.find("\n", self.i)
                if j < 0: j = len(s)
                self._advance(s[self.i:j]); continue
            if s.startswith("/*", self.i):
                j = s.find("*/", self.i + 2)
                if j < 0: raise GoSyntaxError(f"unterminated block comment at {self.line}:{self.col}")
                j += 2
                self._advance(s[self.i:j]); continue
            line, col = self.line, self.col
            if c.isalpha() or c == "_":
                j = self.i + 1
                while j < len(s) and (s[j].isalnum() or s[j] == "_"): j += 1
                v = s[self.i:j]
                self._advance(v)
                self._emit("keyword" if v in KEYWORDS else "ident", v, line, col)
                continue
            if c.isdigit():
                m = re.match(r"(?:0[xX][0-9a-fA-F](?:_?[0-9a-fA-F])*|0[bB][01](?:_?[01])*|0[oO][0-7](?:_?[0-7])*|(?:[0-9](?:_?[0-9])*)(?:\.[0-9](?:_?[0-9])*)?(?:[eE][+-]?[0-9](?:_?[0-9])*)?[i]?)", s[self.i:])
                if not m: raise GoSyntaxError(f"bad number at {line}:{col}")
                v = m.group(0); self._advance(v); self._emit("number", v, line, col); continue
            if c in "\"'`":
                q = c; j = self.i + 1
                while j < len(s):
                    if q != '`' and s[j] == '\\': j += 2; continue
                    if s[j] == q: j += 1; break
                    j += 1
                else: raise GoSyntaxError(f"unterminated literal at {line}:{col}")
                v = s[self.i:j]; self._advance(v); self._emit("string" if q != "'" else "rune", v, line, col); continue
            op = next((x for x in MULTI_OPS if s.startswith(x, self.i)), None)
            if op:
                self._advance(op); self._emit("op", op, line, col); continue
            if c in SINGLE:
                self._advance(c); self._emit("op", c, line, col); continue
            raise GoSyntaxError(f"unexpected character {c!r} at {line}:{col}")
        self.tokens.append(Token("eof", "", self.line, self.col))
        return self.tokens


# ------------------------------- AST ---------------------------------------

@dataclass
class Node:
    line: int

@dataclass
class File(Node):
    package: str
    imports: List[Any] = field(default_factory=list)
    declarations: List[Any] = field(default_factory=list)

@dataclass
class Import(Node):
    path: str
    name: Optional[str] = None

@dataclass
class TypeSpec(Node):
    name: str
    type_expr: Any

@dataclass
class VarSpec(Node):
    names: List[str]
    type_expr: Any = None
    values: List[Any] = field(default_factory=list)

@dataclass
class ConstSpec(Node):
    names: List[str]
    type_expr: Any = None
    values: List[Any] = field(default_factory=list)

@dataclass
class FuncDecl(Node):
    name: str
    receiver: Any = None
    params: List[Any] = field(default_factory=list)
    results: List[Any] = field(default_factory=list)
    body: Any = None

@dataclass
class InterfaceType(Node):
    methods: List[Any] = field(default_factory=list)
    embeds: List[Any] = field(default_factory=list)

@dataclass
class StructType(Node):
    fields: List[Any] = field(default_factory=list)

@dataclass
class Field(Node):
    names: List[str]
    type_expr: Any
    tag: Optional[str] = None

@dataclass
class Block(Node):
    statements: List[Any] = field(default_factory=list)

@dataclass
class Expr(Node):
    kind: str
    value: Any
    children: List[Any] = field(default_factory=list)

@dataclass
class SimpleStmt(Node):
    op: str
    left: List[Any] = field(default_factory=list)
    right: List[Any] = field(default_factory=list)

@dataclass
class IfStmt(Node):
    init: Any
    cond: Any
    then: Block
    else_branch: Any = None

@dataclass
class ForStmt(Node):
    init: Any = None
    cond: Any = None
    post: Any = None
    body: Block = None
    range_expr: Any = None
    range_names: List[Any] = field(default_factory=list)

@dataclass
class SwitchStmt(Node):
    init: Any
    tag: Any
    clauses: List[Any] = field(default_factory=list)

@dataclass
class CaseClause(Node):
    expressions: List[Any]
    statements: List[Any] = field(default_factory=list)
    default: bool = False

@dataclass
class SelectStmt(Node):
    clauses: List[Any] = field(default_factory=list)

@dataclass
class CommClause(Node):
    comm: Any
    statements: List[Any] = field(default_factory=list)
    default: bool = False

@dataclass
class BranchStmt(Node):
    keyword: str
    label: Optional[str] = None

@dataclass
class LabelStmt(Node):
    label: str
    statement: Any

@dataclass
class DeferStmt(Node):
    call: Any

@dataclass
class GoStmt(Node):
    call: Any

@dataclass
class ReturnStmt(Node):
    values: List[Any] = field(default_factory=list)


# ------------------------------- parser ------------------------------------

class Parser:
    def __init__(self, source_or_tokens: Sequence[Token] | str):
        self.tokens = Lexer(source_or_tokens).tokenize() if isinstance(source_or_tokens, str) else list(source_or_tokens)
        self.i = 0

    @property
    def t(self) -> Token: return self.tokens[self.i]
    def peek(self, value=None, kind=None):
        t = self.t
        return (value is None or t.value == value) and (kind is None or t.kind == kind)
    def take(self, value=None):
        t = self.t
        if value is not None and t.value != value:
            raise self.error(f"expected {value!r}, got {t.value!r}")
        self.i += 1
        return t
    def maybe(self, value):
        if self.peek(value): self.i += 1; return True
        return False
    def error(self, msg): return GoSyntaxError(f"{msg} at {self.t.line}:{self.t.column}")
    def semi(self): self.maybe(";")

    def parse(self) -> File:
        p = self.take("package")
        pkg = self.take().value
        self.semi()
        imports = []
        while self.peek("import"): imports.extend(self.parse_import_decl())
        decls = []
        while not self.peek(kind="eof"):
            decls.append(self.parse_decl())
        return File(p.line, pkg, imports, decls)

    def parse_import_decl(self):
        self.take("import"); out=[]
        if self.maybe("("):
            while not self.peek(")"):
                line=self.t.line; name=None
                if self.t.kind in ("ident", "keyword") and not self.peek(kind="string"):
                    name=self.take().value
                path=self.take().value
                if self.tokens[self.i-1].kind != "string": raise self.error("expected import path")
                out.append(Import(line, path[1:-1], name)); self.semi()
            self.take(")"); self.semi(); return out
        line=self.t.line; name=None
        if self.t.kind in ("ident","keyword") and self.tokens[self.i+1].kind == "string": name=self.take().value
        path=self.take().value
        if self.tokens[self.i-1].kind != "string": raise self.error("expected import path")
        self.semi(); return [Import(line,path[1:-1],name)]

    def parse_decl(self):
        if self.peek("func"): return self.parse_func()
        if self.peek("type"): return self.parse_type_decl()
        if self.peek("var"): return self.parse_var_decl()
        if self.peek("const"): return self.parse_const_decl()
        raise self.error("expected declaration")

    def parse_type_decl(self):
        line=self.take("type").line
        if self.maybe("("):
            specs=[]
            while not self.peek(")"):
                n=self.take().value; ty=self.parse_type(); specs.append(TypeSpec(line,n,ty)); self.semi()
            self.take(")"); self.semi(); return specs
        n=self.take().value; ty=self.parse_type(); self.semi(); return TypeSpec(line,n,ty)

    def parse_var_decl(self):
        line=self.take("var").line
        if self.maybe("("):
            specs=[]
            while not self.peek(")"):
                specs.append(self.parse_var_spec(line)); self.semi()
            self.take(")"); self.semi(); return specs
        x=self.parse_var_spec(line); self.semi(); return x

    def parse_const_decl(self):
        line=self.take("const").line
        if self.maybe("("):
            specs=[]
            while not self.peek(")"):
                specs.append(self.parse_const_spec(line)); self.semi()
            self.take(")"); self.semi(); return specs
        x=self.parse_const_spec(line); self.semi(); return x

    def parse_var_spec(self, line):
        names=self.parse_ident_list()
        ty=None
        if not self.peek("="): ty=self.parse_type()
        vals=[]
        if self.maybe("="): vals=self.parse_expr_list()
        return VarSpec(line,names,ty,vals)

    def parse_const_spec(self, line):
        names=self.parse_ident_list(); ty=None
        if not self.peek("="): ty=self.parse_type()
        vals=[]
        if self.maybe("="): vals=self.parse_expr_list()
        return ConstSpec(line,names,ty,vals)

    def parse_ident_list(self):
        out=[self.take().value]
        while self.maybe(","): out.append(self.take().value)
        return out

    def parse_func(self):
        line=self.take("func").line; receiver=None
        if self.peek("("):
            # Distinguish method receiver from function parameter list by finding
            # the matching close followed by the function name.
            save=self.i; depth=0; j=self.i
            while j < len(self.tokens):
                if self.tokens[j].value=="(": depth+=1
                elif self.tokens[j].value==")":
                    depth-=1
                    if depth==0: break
                j+=1
            if j+1 < len(self.tokens) and self.tokens[j+1].kind in ("ident","keyword"):
                receiver=self.parse_param_group()
        name=self.take().value
        params=self.parse_param_group()
        results=[]
        if self.peek("("): results=self.parse_param_group()
        elif not self.peek("{"): results=[self.parse_type()]
        body=self.parse_block()
        return FuncDecl(line,name,receiver,params,results,body)

    def parse_param_group(self):
        self.take("("); out=[]
        while not self.peek(")"):
            line=self.t.line; names=[]
            if self.t.kind in ("ident","keyword") and self.tokens[self.i+1].value not in (",", ")", "..."):
                names=self.parse_ident_list()
            variadic=self.maybe("...")
            ty=self.parse_type()
            out.append(Field(line,names,Expr(line,"variadic",True,[ty]) if variadic else ty))
            if not self.maybe(",") and not self.peek(")"): raise self.error("expected ',' in parameter list")
        self.take(")"); return out

    def parse_type(self):
        line=self.t.line
        if self.maybe("*"): return Expr(line,"pointer",None,[self.parse_type()])
        if self.maybe("["):
            if self.maybe("..."): inner=self.parse_type(); self.take("]"); return Expr(line,"array",None,[inner])
            n=None if self.peek("]") else self.parse_expr()
            self.take("]"); return Expr(line,"array",n,[self.parse_type()])
        if self.maybe("chan"):
            direction="both"
            if self.maybe("<-"): direction="recv"
            ty=self.parse_type(); return Expr(line,"chan",direction,[ty])
        if self.maybe("<-"):
            self.take("chan"); return Expr(line,"chan","recv",[self.parse_type()])
        if self.maybe("map"):
            self.take("["); k=self.parse_type(); self.take("]"); v=self.parse_type(); return Expr(line,"map",None,[k,v])
        if self.maybe("struct"):
            self.take("{"); fields=[]
            while not self.peek("}"):
                fl=self.t.line; names=[]
                if self.t.kind in ("ident","keyword") and self.tokens[self.i+1].value not in (";","}"):
                    names=self.parse_ident_list()
                ty=self.parse_type(); tag=None
                if self.t.kind=="string": tag=self.take().value
                fields.append(Field(fl,names,ty,tag)); self.semi()
            self.take("}"); return StructType(line,fields)
        if self.maybe("interface"):
            self.take("{"); methods=[]; embeds=[]
            while not self.peek("}"):
                ml=self.t.line
                if self.t.kind in ("ident","keyword") and self.tokens[self.i+1].value=="(":
                    n=self.take().value; params=self.parse_param_group(); results=[]
                    if self.peek("("): results=self.parse_param_group()
                    elif not self.peek(";") and not self.peek("}"): results=[self.parse_type()]
                    methods.append(FuncDecl(ml,n,None,params,results,None))
                else:
                    embeds.append(self.parse_type())
                self.semi()
            self.take("}"); return InterfaceType(line,methods,embeds)
        if self.t.kind in ("ident","keyword"):
            return Expr(line,"type_name",self.take().value)
        raise self.error("expected type")

    def parse_block(self):
        line=self.take("{").line; stmts=[]
        while not self.peek("}"):
            if self.peek(kind="eof"): raise self.error("unterminated block")
            stmts.append(self.parse_stmt()); self.semi()
        self.take("}"); return Block(line,stmts)

    def parse_stmt(self):
        t=self.t
        if self.peek("{"): return self.parse_block()
        if self.peek("if"): return self.parse_if()
        if self.peek("for"): return self.parse_for()
        if self.peek("switch"): return self.parse_switch()
        if self.peek("select"): return self.parse_select()
        if self.peek("return"):
            self.take(); vals=[] if self.peek(";") or self.peek("}") else self.parse_expr_list(); return ReturnStmt(t.line,vals)
        if self.peek("defer"): self.take(); return DeferStmt(t.line,self.parse_call_expr())
        if self.peek("go"): self.take(); return GoStmt(t.line,self.parse_call_expr())
        if self.peek("break") or self.peek("continue") or self.peek("goto") or self.peek("fallthrough"):
            kw=self.take().value; label=None
            if self.t.kind == "ident" and not self.peek(";") and not self.peek("}"): label=self.take().value
            return BranchStmt(t.line,kw,label)
        # label: statement
        if self.t.kind=="ident" and self.tokens[self.i+1].value==":":
            label=self.take().value; self.take(":"); return LabelStmt(t.line,label,self.parse_stmt())
        return self.parse_simple_stmt()

    def parse_if(self):
        line=self.take("if").line; init=None
        first=self.parse_simple_stmt_or_expr()
        if self.maybe(";"): init=first; cond=self.parse_expr()
        else: cond=first
        then=self.parse_block(); other=None
        if self.maybe("else"):
            other=self.parse_if() if self.peek("if") else self.parse_block()
        return IfStmt(line,init,cond,then,other)

    def parse_for(self):
        line=self.take("for").line
        if self.peek("{"): return ForStmt(line,body=self.parse_block())
        # Recognize `for k, v := range expr` / `for k := range expr`
        # before attempting the general three-part form.
        save=self.i
        if self.t.kind in ("ident", "keyword"):
            j=self.i
            while j < len(self.tokens) and self.tokens[j].kind in ("ident", "keyword"):
                j += 1
                if j < len(self.tokens) and self.tokens[j].value == ",":
                    j += 1
                    if j < len(self.tokens) and self.tokens[j].kind in ("ident", "keyword"):
                        j += 1
                    else:
                        break
                else:
                    break
            if j < len(self.tokens) and self.tokens[j].value in (":=", "=") and j + 1 < len(self.tokens) and self.tokens[j+1].value == "range":
                lhs=[]
                while self.t.value != ":=" and self.t.value != "=":
                    lhs.append(self.take().value)
                    if not self.maybe(","): break
                self.take()
                self.take("range")
                if self.t.kind in ("ident", "keyword") and self.tokens[self.i+1].value == "{":
                    expr=Expr(self.t.line, "name", self.take().value)
                else:
                    expr=self.parse_expr()
                return ForStmt(line,body=self.parse_block(),range_expr=expr,range_names=lhs)
        self.i=save
        init=None; cond=None; post=None
        first=self.parse_simple_stmt_or_expr()
        if self.maybe(";"):
            init=first
            if not self.peek(";"): cond=self.parse_expr()
            self.take(";")
            if not self.peek("{"): post=self.parse_simple_stmt()
        else: cond=first
        return ForStmt(line,init,cond,post,self.parse_block())

    def parse_switch(self):
        line=self.take("switch").line; init=None; tag=None
        if not self.peek("{"):
            # A bare identifier immediately followed by the switch body is
            # the switch tag (e.g. `switch x {`), not a composite literal.
            if self.t.kind in ("ident", "keyword") and self.tokens[self.i+1].value == "{":
                first=Expr(self.t.line, "name", self.take().value)
            else:
                first=self.parse_simple_stmt_or_expr()
            if self.maybe(";"): init=first; tag=None if self.peek("{") else self.parse_expr()
            else: tag=first
        self.take("{"); clauses=[]
        while not self.peek("}"):
            cl=self.t.line
            if self.maybe("case"): ex=self.parse_expr_list(); self.take(":"); default=False
            elif self.maybe("default"): ex=[]; self.take(":"); default=True
            else: raise self.error("expected case/default")
            stmts=[]
            while not self.peek("case") and not self.peek("default") and not self.peek("}"):
                stmts.append(self.parse_stmt()); self.semi()
            clauses.append(CaseClause(cl,ex,stmts,default))
        self.take("}"); return SwitchStmt(line,init,tag,clauses)

    def parse_select(self):
        line=self.take("select").line; self.take("{"); clauses=[]
        while not self.peek("}"):
            cl=self.t.line; default=False
            if self.maybe("case"): comm=self.parse_simple_stmt(); self.take(":")
            elif self.maybe("default"): comm=None; default=True; self.take(":")
            else: raise self.error("expected select case/default")
            stmts=[]
            while not self.peek("case") and not self.peek("default") and not self.peek("}"):
                stmts.append(self.parse_stmt()); self.semi()
            clauses.append(CommClause(cl,comm,stmts,default))
        self.take("}"); return SelectStmt(line,clauses)

    def parse_simple_stmt_or_expr(self):
        # Communication statements and assignments have expression lists on
        # their left-hand side (e.g. `v, ok := <-ch`).  Parse the first
        # expression and extend it only when a comma is actually present.
        left=[self.parse_expr()]
        if self.peek(","):
            left.extend(self.parse_expr_list())
        if self.t.value in (":=", "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "&^=", "++", "--", "<-"):
            op=self.take().value
            if op in ("++","--"): return SimpleStmt(left[0].line,op,left,[])
            return SimpleStmt(left[0].line,op,left,self.parse_expr_list())
        if len(left) > 1:
            raise self.error("expected assignment or communication operator after expression list")
        return left[0]

    def parse_simple_stmt(self): return self.parse_simple_stmt_or_expr()

    def parse_expr_list(self):
        out=[self.parse_expr()]
        while self.maybe(","): out.append(self.parse_expr())
        return out

    PRECEDENCE={"||":1,"&&":2,"==":3,"!=":3,"<":4,"<=":4,">":4,">=":4,"|":5,"^":6,"&":7,"<<":8,">>":8,"&^":8,"+":9,"-":9,"*":10,"/":10,"%":10}
    def parse_expr(self, min_prec=0):
        left=self.parse_unary()
        while self.t.value in self.PRECEDENCE and self.PRECEDENCE[self.t.value] >= min_prec:
            op=self.take().value; prec=self.PRECEDENCE[op]; right=self.parse_expr(prec+1)
            left=Expr(left.line,"binary",op,[left,right])
        return left

    def parse_unary(self):
        t=self.t
        if t.value in ("+","-","!","^","*","&","<-", "~"):
            op=self.take().value; return Expr(t.line,"unary",op,[self.parse_unary()])
        return self.parse_primary()

    def parse_primary(self):
        t=self.t
        if t.value=="(":
            self.take(); x=self.parse_expr(); self.take(")"); return self.parse_postfix(x)
        if t.kind in ("number","string","rune"):
            self.take(); return self.parse_postfix(Expr(t.line,"literal",t.value))
        if t.kind in ("ident","keyword"):
            self.take(); x=Expr(t.line,"name",t.value)
            if self.peek("{") and t.value not in KEYWORDS:
                # composite literal: T{...}
                self.take(); elems=[]
                while not self.peek("}"):
                    elems.append(self.parse_expr())
                    if not self.maybe(","): break
                self.take("}"); x=Expr(t.line,"composite",x,[*elems])
            return self.parse_postfix(x)
        if t.value=="[": raise self.error("unexpected '[' in expression")
        raise self.error("expected expression")

    def parse_postfix(self,x):
        while True:
            if self.maybe("("):
                args=[]
                while not self.peek(")"):
                    args.append(self.parse_expr())
                    if not self.maybe(","): break
                self.take(")"); x=Expr(x.line,"call",None,[x,*args]); continue
            if self.maybe("["):
                idx=self.parse_expr(); self.take("]"); x=Expr(x.line,"index",None,[x,idx]); continue
            if self.maybe("."):
                name=self.take().value; x=Expr(x.line,"selector",name,[x]); continue
            break
        return x

    def parse_call_expr(self):
        x=self.parse_primary()
        if x.kind != "call": raise self.error("expected function call")
        return x


def parse_go(source: str) -> File:
    return Parser(source).parse()


def walk(node):
    """Yield AST nodes depth-first; useful for later lowering/analysis."""
    if isinstance(node, Node):
        yield node
        for value in vars(node).values():
            yield from walk(value)
    elif isinstance(node, (list, tuple)):
        for x in node: yield from walk(x)
    elif isinstance(node, dict):
        for x in node.values(): yield from walk(x)
