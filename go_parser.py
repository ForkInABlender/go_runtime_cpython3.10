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
                if self.tokens and self.tokens[-1].value in (
                    ")", "]", "}", "++", "--",
                    "break", "continue", "fallthrough", "return"
                ) or (self.tokens and self.tokens[-1].kind in ("ident", "number", "string", "rune")):
                    last=self.tokens[-1]
                    self.tokens.append(Token("op", ";", last.line, last.column + max(1, len(last.value))))
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
            self.semi()
            if self.peek(kind="eof"):
                break
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
        n=self.take().value
        if self.peek("["):
            depth=0
            while self.i < len(self.tokens):
                v=self.take().value
                if v == "[": depth += 1
                elif v == "]":
                    depth -= 1
                    if depth == 0: break
        # Go type aliases use `type Name = ExistingType`.  The IR represents
        # aliases and defined types with the same TypeSpec node; consume the
        # alias marker so the underlying type can still be parsed normally.
        self.maybe("=")
        ty=self.parse_type(); self.semi(); return TypeSpec(line,n,ty)

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
        if self.peek(";") or self.peek(")"):
            return ConstSpec(line,names,None,[])
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
        if self.peek("["):
            # Generic type-parameter list: func F[T any](x T) ...
            depth=0
            while self.i < len(self.tokens):
                v=self.take().value
                if v == "[": depth += 1
                elif v == "]":
                    depth -= 1
                    if depth == 0: break
        params=self.parse_param_group()
        results=[]
        if self.peek("("): results=self.parse_param_group()
        elif not self.peek("{") and not self.peek(";"): results=[self.parse_type()]
        if self.peek(";"):
            self.take(";")
            return FuncDecl(line,name,receiver,params,results,None)
        body=self.parse_block()
        return FuncDecl(line,name,receiver,params,results,body)

    def parse_param_group(self):
        self.take("("); out=[]
        type_starters={"*", "[", "func", "chan", "<-", "map", "struct", "interface"}
        while not self.peek(")"):
            line=self.t.line
            names=[]

            # Go parameter declarations have an important ambiguity:
            #   func(rune, rune)        -- two unnamed parameter types
            #   func(a, b int)          -- two named parameters
            # Decide whether an identifier is a name by looking past a comma
            # to see whether the following identifier is itself followed by a
            # type token.
            if self.t.kind in ("ident", "keyword"):
                n0=self.tokens[self.i+1].value if self.i+1 < len(self.tokens) else None
                named = (
                    n0 in type_starters
                    or (self.tokens[self.i+1].kind in ("ident", "keyword") if self.i+1 < len(self.tokens) else False)
                )
                if n0 == "...":
                    named = True
                elif n0 == "," and self.i+3 < len(self.tokens):
                    # a, b int  -> named; rune, rune -> unnamed
                    named = (
                        self.tokens[self.i+2].kind in ("ident", "keyword")
                        and self.tokens[self.i+3].value not in (",", ")", "...")
                    )
                if named:
                    names.append(self.take().value)
                    while self.maybe(","):
                        if self.t.kind not in ("ident", "keyword"):
                            break
                        # The next identifier is another name only when what
                        # follows it begins a type declaration.
                        nxt=self.tokens[self.i+1].value if self.i+1 < len(self.tokens) else None
                        if nxt == "..." or nxt in type_starters or (
                            self.i+1 < len(self.tokens)
                            and self.tokens[self.i+1].kind in ("ident", "keyword")
                        ):
                            names.append(self.take().value)
                            continue
                        break

            variadic=self.maybe("...")
            ty=self.parse_type()
            out.append(Field(line,names,Expr(line,"variadic",True,[ty]) if variadic else ty))
            if not self.maybe(",") and not self.peek(")"):
                raise self.error("expected ',' in parameter list")
        self.take(")"); return out

    def parse_type(self):
        line=self.t.line
        if self.maybe("*"): return Expr(line,"pointer",None,[self.parse_type()])
        if self.maybe("func"):
            params=self.parse_param_group()
            results=[]
            if self.peek("("): results=self.parse_param_group()
            elif not self.peek("{") and not self.peek(")") and not self.peek(";") and not self.peek("}") and not self.peek(",") and not self.peek("...") and self.t.kind not in ("eof",):
                # A single unnamed result type, e.g. `func() bool`.
                results=[self.parse_type()]
            return Expr(line,"func_type",None,[params, results])
        if self.maybe("["):
            if self.maybe("..."): self.take("]"); return Expr(line,"array",None,[self.parse_type()])
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
                # Only treat the leading identifier as a field name list when
                # it is NOT a qualified embedded type (e.g. `sys.NotInHeap`).
                # A dot after the first ident means it is a package-qualified
                # embedded type, not a name.
                if (self.t.kind in ("ident","keyword")
                        and self.tokens[self.i+1].value not in (";","}", ".")
                        and self.tokens[self.i+1].kind not in ("eof",)):
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
                    elif (self.t.kind in ("ident", "keyword") and self.i + 1 < len(self.tokens) and self.tokens[self.i + 1].value == "("):
                        results=[]
                    elif not self.peek(";") and not self.peek("}"): results=[self.parse_type()]
                    methods.append(FuncDecl(ml,n,None,params,results,None))
                else:
                    # Type constraint: ~T, T | U, or embedded interface type.
                    # Consume a union of types separated by `|`.
                    self.maybe("~")  # tilde = underlying-type constraint; ignore for IR
                    embed=self.parse_type()
                    while self.maybe("|"):
                      
