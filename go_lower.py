"""Lower the AST produced by go_parser into executable Python source.

This is deliberately a lowering pass, not a Go compiler.  It targets the
Python runtime primitives already provided by goruntime.py and the small
source-translation helpers (switch_case.py and goto.py).
"""
from __future__ import annotations

import keyword
import re
from typing import Any, Dict, List, Optional

from go_parser import (
    Block, BranchStmt, CaseClause, CommClause, ConstSpec, DeferStmt,
    Expr, Field, File, ForStmt, FuncDecl, GoStmt, IfStmt, InterfaceType,
    LabelStmt, ReturnStmt, SelectStmt, SimpleStmt, StructType, SwitchStmt,
    TypeSpec, VarSpec,
)


class LoweringError(Exception):
    pass


GO_TO_PY = {
    "true": "True", "false": "False", "nil": "None",
    "iota": "__go_iota__",
}

# Go operators whose Python spelling/semantics differ.
BIN_OP = {"&&": "and", "||": "or", "&^": "&~"}
UNARY_OP = {"!": "not ", "^": "~", "<-": "go_recv"}


def py_ident(name: str) -> str:
    """Map a Go identifier to a legal, collision-resistant Python name."""
    if name in GO_TO_PY:
        return GO_TO_PY[name]
    if keyword.iskeyword(name):
        return f"go_{name}"
    return name


class Lowerer:
    def __init__(self, module_name: str = "translated_go"):
        self.module_name = module_name
        self.lines: List[str] = []
        self.indent = 0
        self.iota = 0
        self.labels: Dict[str, int] = {}
        self._needs: set[str] = set()
        self._function_depth = 0
        self._package_names: set[str] = set()
        self._label_names: set[str] = set()
        self._select_callback = False

    def emit(self, text: str = "") -> None:
        self.lines.append("    " * self.indent + text)

    def require(self, name: str) -> None:
        self._needs.add(name)

    def lower(self, tree: File) -> str:
        self.lines = []
        self.indent = 0
        self.iota = 0
        self.labels = {}
        self._needs.clear()
        self._package_names = set()
        self._label_names = set()
        for d in tree.declarations:
            items = d if isinstance(d, list) else [d]
            for item in items:
                if isinstance(item, (VarSpec, ConstSpec)):
                    self._package_names.update(item.names)
        self._scan_needs(tree)

        self.emit('"""Generated Python from Go AST."""')
        self.emit("from __future__ import annotations")
        self.emit()
        if self._needs:
            imports = []
            if "runtime" in self._needs:
                imports.append("import goruntime as _go_runtime")
            if "goto" in self._needs:
                imports.append("from goto import Goto as _GoGoto")
                imports.append("_go_runtime_goto = _GoGoto")
            for imp in imports:
                self.emit(imp)
            self.emit()

        self.emit(f"__go_package__ = {tree.package!r}")
        if any(isinstance(n, ForStmt) and n.range_expr is not None for n in self._walk(tree)):
            self.emit("def _go_range(x):")
            self.indent += 1
            self.emit("return x.items() if isinstance(x, dict) else enumerate(x)")
            self.indent -= 1
            self.emit()
        for imp in tree.imports:
            self.emit(f"# Go import: {imp.path!r}" + (f" as {imp.name}" if imp.name else ""))
        if tree.imports:
            self.emit()
        for decl in tree.declarations:
            if isinstance(decl, list):
                for d in decl:
                    self.lower_decl(d)
            else:
                self.lower_decl(decl)
        return "\n".join(self.lines) + "\n"

    def _scan_needs(self, tree: File) -> None:
        for n in self._walk(tree):
            if isinstance(n, (GoStmt, DeferStmt, SelectStmt)):
                self.require("runtime")
            if isinstance(n, SwitchStmt):
                self.require("switch")
            if isinstance(n, (BranchStmt, LabelStmt)) and (getattr(n, "keyword", None) == "goto" or isinstance(n, LabelStmt)):
                self.require("goto")
            if isinstance(n, InterfaceType):
                self.require("interface")

    def _walk(self, value):
        if isinstance(value, list):
            for x in value:
                yield from self._walk(x)
        elif isinstance(value, tuple):
            for x in value:
                yield from self._walk(x)
        elif hasattr(value, "__dataclass_fields__"):
            yield value
            for x in vars(value).values():
                yield from self._walk(x)

    def lower_decl(self, d: Any) -> None:
        if isinstance(d, FuncDecl):
            self.lower_func(d)
        elif isinstance(d, TypeSpec):
            self.lower_type(d)
        elif isinstance(d, VarSpec):
            self.lower_var(d)
        elif isinstance(d, ConstSpec):
            self.lower_const(d)
        else:
            raise LoweringError(f"unsupported declaration: {type(d).__name__}")

    def lower_func(self, d: FuncDecl) -> None:
        receiver = d.receiver
        params: List[str] = []
        if receiver:
            for f in receiver:
                for n in f.names:
                    params.append(py_ident(n))
        for f in d.params:
            names = f.names or [f"arg{len(params)}"]
            for n in names:
                params.append(py_ident(n))
        self.emit(f"def {py_ident(d.name)}({', '.join(params)}):")
        self.indent += 1
        if self._package_names:
            self.emit("global " + ", ".join(py_ident(n) for n in sorted(self._package_names)))
        self._function_depth += 1
        labels = self._collect_labels(d.body) if d.body else []
        if labels:
            # A local dispatch loop gives goto real function-local semantics
            # instead of relying on goto.py's module-global label registry.
            self.require("goto")
            self.emit("__go_pc = None")
            self.emit("while True:")
            self.indent += 1
            self.emit("try:")
            self.indent += 1
            self.lower_block_with_goto(d.body, labels)
            self.emit("break")
            self.indent -= 1
            self.emit("except _go_runtime_goto as __go_jump:")
            self.indent += 1
            self.emit("__go_pc = __go_jump.args[0]")
            self.emit("continue")
            self.indent -= 1
            self.indent -= 1
        elif not d.body or not d.body.statements:
            self.emit("pass")
        else:
            for s in d.body.statements:
                self.lower_stmt(s)
        self._function_depth -= 1
        self.indent -= 1
        self.emit()

    def _collect_labels(self, block: Optional[Block]) -> List[str]:
        found=[]
        for n in self._walk(block):
            if isinstance(n, LabelStmt) and n.label not in found:
                found.append(n.label)
        return found

    def lower_block_with_goto(self, block: Block, labels: List[str]) -> None:
        # Emit a dispatcher around labeled statements.  Non-labeled code runs
        # normally; a goto raises the lightweight local jump exception.
        for s in block.statements:
            if isinstance(s, LabelStmt):
                self.emit(f"if __go_pc not in (None, {s.label!r}):")
                self.indent += 1
                self.emit("pass")
                self.indent -= 1
                self.emit(f"if __go_pc == {s.label!r}:")
                self.indent += 1
                self.lower_stmt(s.statement)
                self.indent -= 1
                self.emit("__go_pc = None")
            else:
                self.lower_stmt(s)

    def lower_type(self, d: TypeSpec) -> None:
        t = d.type_expr
        if isinstance(t, StructType):
            self.emit(f"class {py_ident(d.name)}:")
            self.indent += 1
            fields = [n for f in t.fields for n in f.names]
            if fields:
                self.emit("def __init__(self, " + ", ".join(py_ident(x) for x in fields) + "):")
                self.indent += 1
                for n in fields:
                    self.emit(f"self.{py_ident(n)} = {py_ident(n)}")
                self.indent -= 1
            else:
                self.emit("pass")
            self.indent -= 1
        elif isinstance(t, InterfaceType):
            self.emit(f"class {py_ident(d.name)}:")
            self.indent += 1
            if t.embeds:
                self.emit("# embedded interfaces: " + ", ".join(self.expr(x) for x in t.embeds))
            for m in t.methods:
                params = [py_ident(n) for f in m.params for n in (f.names or [f"arg{len(params) if 'params' in locals() else 0}"])]
                self.emit(f"def {py_ident(m.name)}({', '.join(['self'] + params)}):")
                self.indent += 1
                self.emit("raise NotImplementedError")
                self.indent -= 1
            if not t.methods:
                self.emit("pass")
            self.indent -= 1
        else:
            self.emit(f"{py_ident(d.name)} = {self.type_expr(t)!r}")

    def lower_var(self, d: VarSpec) -> None:
        vals = [self.expr(x) for x in d.values]
        if not vals:
            vals = ["None"] * len(d.names)
        if len(d.names) == 1:
            self.emit(f"{py_ident(d.names[0])} = {vals[0]}")
        else:
            rhs = ", ".join(vals)
            self.emit(f"{', '.join(py_ident(n) for n in d.names)} = {rhs}")

    def lower_const(self, d: ConstSpec) -> None:
        self.lower_var(VarSpec(d.line, d.names, d.type_expr, d.values))

    def lower_block(self, b: Block) -> None:
        for s in b.statements:
            self.lower_stmt(s)

    def lower_stmt(self, s: Any) -> None:
        if isinstance(s, Block):
            self.lower_block(s)
        elif isinstance(s, SimpleStmt):
            self.lower_simple(s)
        elif isinstance(s, IfStmt):
            self.emit(f"if {self.expr(s.cond)}:")
            self.indent += 1; self.lower_block(s.then); self.indent -= 1
            if s.else_branch:
                self.emit("else:")
                self.indent += 1
                if isinstance(s.else_branch, IfStmt): self.lower_stmt(s.else_branch)
                else: self.lower_block(s.else_branch)
                self.indent -= 1
        elif isinstance(s, ForStmt):
            self.lower_for(s)
        elif isinstance(s, SwitchStmt):
            self.lower_switch(s)
        elif isinstance(s, SelectStmt):
            self.lower_select(s)
        elif isinstance(s, ReturnStmt):
            if self._select_callback:
                if not s.values:
                    self.emit("__go_result = None")
                elif len(s.values) == 1:
                    self.emit(f"__go_result = {self.expr(s.values[0])}")
                else:
                    self.emit("__go_result = (" + ", ".join(self.expr(x) for x in s.values) + ")")
                self.emit("return")
            elif not s.values: self.emit("return")
            elif len(s.values) == 1: self.emit(f"return {self.expr(s.values[0])}")
            else: self.emit("return " + ", ".join(self.expr(x) for x in s.values))
        elif isinstance(s, DeferStmt):
            self.emit(f"_go_runtime.defer(lambda: {self.expr(s.call)})")
        elif isinstance(s, GoStmt):
            self.emit(f"_go_runtime.go(lambda: {self.expr(s.call)})")
        elif isinstance(s, BranchStmt):
            if s.keyword == "goto":
                self.emit(f"raise _go_runtime_goto({s.label!r})")
            elif s.keyword == "fallthrough":
                self.emit("# Go fallthrough")
            else:
                self.emit(s.keyword)
        elif isinstance(s, LabelStmt):
            self.emit(f"@label({s.label!r})")
            self.emit("def __go_label():")
            self.indent += 1
            self.lower_stmt(s.statement)
            self.indent -= 1
            self.emit("__go_label()")
        else:
            raise LoweringError(f"unsupported statement: {type(s).__name__}")

    def lower_simple(self, s: SimpleStmt) -> None:
        if s.op in ("++", "--"):
            op = "+=" if s.op == "++" else "-="
            self.emit(f"{self.expr(s.left[0])} {op} 1")
            return
        left = ", ".join(self.expr(x) for x in s.left)
        if s.op == "<-":
            self.emit(f"{self.expr(s.left[0])}.send({self.expr(s.right[0])})")
        else:
            op = "=" if s.op == ":=" else s.op
            self.emit(f"{left} {op} " + ", ".join(self.expr(x) for x in s.right))

    def lower_for(self, s: ForStmt) -> None:
        if s.range_expr is not None:
            names = [py_ident(x.value) if isinstance(x, Expr) and x.kind == "name" else py_ident(str(x)) for x in s.range_names]
            target = ", ".join(names) or "_"
            source = self.expr(s.range_expr)
            if len(names) >= 2:
                self.emit(f"for {names[0]}, {names[1]} in _go_range({source}):")
            else:
                self.emit(f"for {target} in {source}:")
            self.indent += 1; self.lower_block(s.body); self.indent -= 1
            return
        if s.init is not None and s.cond is not None and s.post is not None:
            self.lower_simple(s.init)
            self.emit(f"while {self.expr(s.cond)}:")
            self.indent += 1; self.lower_block(s.body); self.lower_simple(s.post); self.indent -= 1
        elif s.cond is not None:
            self.emit(f"while {self.expr(s.cond)}:")
            self.indent += 1; self.lower_block(s.body); self.indent -= 1
        else:
            self.emit("while True:")
            self.indent += 1; self.lower_block(s.body); self.indent -= 1

    def lower_switch(self, s: SwitchStmt) -> None:
        # Lower Go's first-match switch semantics to an if/elif chain.
        # `fallthrough` is handled by inlining the immediately following case,
        # which is the only implicit control transfer Go permits here.
        if s.init is not None:
            self.lower_simple(s.init)
        tag = self.expr(s.tag) if s.tag is not None else "True"
        clauses = s.clauses

        def emit_case_body(index: int) -> None:
            c = clauses[index]
            stmts = list(c.statements)
            fall = bool(stmts and isinstance(stmts[-1], BranchStmt) and stmts[-1].keyword == "fallthrough")
            if fall:
                stmts.pop()
            self.lower_block(Block(c.line, stmts))
            if fall and index + 1 < len(clauses):
                emit_case_body(index + 1)

        first = True
        for i, c in enumerate(clauses):
            cond = "True" if c.default else " or ".join(f"{tag} == {self.expr(x)}" for x in c.expressions)
            self.emit(("if " if first else "elif ") + cond + ":")
            self.indent += 1
            emit_case_body(i)
            self.indent -= 1
            first = False

    def lower_select(self, s: SelectStmt) -> None:
        self.emit("__go_result = None")
        self.emit("_go_select_cases = []")
        for i, c in enumerate(s.clauses):
            fn = f"__go_select_case_{i}"
            if c.default:
                self.emit(f"def {fn}():")
                self.indent += 1
                self.emit("nonlocal __go_result")
                old_mode = self._select_callback; self._select_callback = True
                self.lower_block(Block(c.line, c.statements))
                self._select_callback = old_mode
                if not c.statements: self.emit("pass")
                self.indent -= 1
                self.emit(f"_go_select_cases.append(_go_runtime.case_default({fn}))")
                continue
            comm = c.comm
            if not isinstance(comm, SimpleStmt):
                raise LoweringError("select communication clause must be a simple statement")
            if comm.op == "<-":
                self.emit(f"def {fn}():")
                self.indent += 1
                self.emit("nonlocal __go_result")
                old_mode = self._select_callback; self._select_callback = True
                self.lower_block(Block(c.line, c.statements))
                self._select_callback = old_mode
                if not c.statements: self.emit("pass")
                self.indent -= 1
                self.emit(f"_go_select_cases.append(_go_runtime.case_send({self.expr(comm.left[0])}, {self.expr(comm.right[0])}, {fn}))")
                continue
            if comm.op in (":=", "=") and len(comm.right) == 1:
                recv = comm.right[0]
                if isinstance(recv, Expr) and recv.kind == "unary" and recv.value == "<-":
                    ch = self.expr(recv.children[0])
                    self.emit(f"def {fn}(__go_value):")
                    self.indent += 1
                    self.emit("nonlocal __go_result")
                    old_mode = self._select_callback; self._select_callback = True
                    if len(comm.left) >= 1:
                        self.emit(f"{self.expr(comm.left[0])} = __go_value")
                    if len(comm.left) >= 2:
                        self.emit(f"{self.expr(comm.left[1])} = True")
                    self.lower_block(Block(c.line, c.statements))
                    self._select_callback = old_mode
                    if not c.statements and not comm.left: self.emit("pass")
                    self.indent -= 1
                    self.emit(f"_go_select_cases.append(_go_runtime.case_recv({ch}, {fn}))")
                    continue
            raise LoweringError(f"unsupported select communication: {comm.op}")
        self.emit("_go_runtime.select(*_go_select_cases)")
        self.emit("del _go_select_cases")
        self.emit("return __go_result")

    def expr(self, x: Any) -> str:
        if isinstance(x, Expr):
            k = x.kind
            if k == "name": return py_ident(str(x.value))
            if k == "literal": return self.literal(str(x.value))
            if k == "type_name": return py_ident(str(x.value))
            if k == "variadic": return self.expr(x.children[0])
            if k == "binary":
                op = BIN_OP.get(x.value, x.value)
                return f"({self.expr(x.children[0])} {op} {self.expr(x.children[1])})"
            if k == "unary":
                op = UNARY_OP.get(x.value, x.value)
                if x.value == "<-": return f"{self.expr(x.children[0])}.recv()"
                return f"({op}{self.expr(x.children[0])})"
            if k == "call":
                fn = self.expr(x.children[0])
                raw_args = x.children[1:]
                if isinstance(x.children[0], Expr) and x.children[0].kind == "name":
                    if x.children[0].value == "make" and raw_args and isinstance(raw_args[0], Expr) and raw_args[0].kind == "chan":
                        cap = self.expr(raw_args[1]) if len(raw_args) > 1 else "0"
                        return f"_go_runtime.Channel(capacity={cap})"
                    if x.children[0].value == "new" and raw_args:
                        return "None"
                args = ", ".join(self.expr(a) for a in raw_args)
                return f"{fn}({args})"
            if k == "index": return f"{self.expr(x.children[0])}[{self.expr(x.children[1])}]"
            if k == "selector": return f"{self.expr(x.children[0])}.{py_ident(x.value)}"
            if k == "composite":
                return "{" + ", ".join(self.expr(a) for a in x.children) + "}"
            if k == "array": return self.type_expr(x)
            if k == "chan": return "Channel()"
            if k == "pointer": return self.type_expr(x)
            if k == "map": return "dict"
        if isinstance(x, str): return py_ident(x)
        return repr(x)

    def literal(self, text: str) -> str:
        if text.endswith("i") and re.match(r"^[0-9]", text):
            return text[:-1] + "j"
        if text.startswith("`"):
            return repr(text[1:-1])
        if text.startswith("'"):
            body = text[1:-1]
            return repr(body)
        return text.replace("_", "")

    def type_expr(self, t: Any) -> str:
        if isinstance(t, Expr):
            if t.kind == "type_name": return py_ident(str(t.value))
            if t.kind == "pointer": return f"Optional[{self.type_expr(t.children[0])}]"
            if t.kind == "array": return f"list[{self.type_expr(t.children[0])}]"
            if t.kind == "chan": return "Channel"
            if t.kind == "map": return "dict"
        if isinstance(t, StructType): return "dict"
        if isinstance(t, InterfaceType): return "object"
        return "object"


def lower_go(tree: File, module_name: str = "translated_go") -> str:
    return Lowerer(module_name).lower(tree)


def translate_go(source: str, module_name: str = "translated_go") -> str:
    from go_parser import parse_go
    return lower_go(parse_go(source), module_name)
