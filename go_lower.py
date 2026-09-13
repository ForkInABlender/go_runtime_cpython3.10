"""Lower the AST produced by go_parser into executable Python source.

This is deliberately a lowering pass, not a Go compiler.  It targets the
Python runtime primitives already provided by goruntime.py and the small
source-translation helpers (switch_case.py and goto.py).
"""
from __future__ import annotations

import importlib
import ast
import os
import sys
from pathlib import Path
import keyword
import os
import re
import subprocess
import re
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set

from go_parser import (
    Block, BranchStmt, CaseClause, CommClause, ConstSpec, DeferStmt,
    Expr, Field, File, ForStmt, FuncDecl, GoStmt, IfStmt, Import, InterfaceType,
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
    # Go predeclared literals (`true`, `false`, `nil`) are handled explicitly
    # by expression lowering.  When the same spelling occurs in a parameter
    # or field position, however, Python requires a legal identifier.
    if name in GO_TO_PY and GO_TO_PY[name] in {"True", "False", "None"}:
        return f"go_{name}"
    if keyword.iskeyword(name):
        return f"go_{name}"
    if name in GO_TO_PY:
        return GO_TO_PY[name]
    if keyword.iskeyword(name):
        return f"go_{name}"
    return name


class Lowerer:
    def __init__(
        self,
        module_name: str = "translated_go",
        runtime_bindings: Optional[Mapping[str, str]] = None,
        import_paths: Optional[Sequence[str]] = None,
    ):
        self.module_name = module_name
        self.runtime_bindings = dict(runtime_bindings or {})
        self.import_paths = list(import_paths or ())
        self.lines: List[str] = []
        self.indent = 0
        self.iota = 0
        self.labels: Dict[str, int] = {}
        self._needs: set[str] = set()
        self._function_depth = 0
        self._package_names: set[str] = set()
        self._label_names: set[str] = set()
        self._select_callback = False
        self._loop_depth = 0
        self._break_depth = 0
        self._last_const_values = None
        self._method_bindings: List[tuple[str, str, str]] = []
        self._top_level_decls: List[Any] = []

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
        self.emit("from typing import Optional")
        self.emit("def _go_len(x):")
        self.indent += 1
        self.emit("return 0 if _go_builtins.isinstance(x, _go_builtins.type) else _go_builtins.len(x)")
        self.indent -= 1
        self.emit("import builtins as _go_builtins")
        self.emit("_go_select_break = _go_builtins.object()")
        self.emit("_go_select_continue = _go_builtins.object()")
        self.emit("def _go_cap(x):")
        self.indent += 1
        self.emit("return 0 if _go_builtins.isinstance(x, _go_builtins.type) else _go_builtins.len(x)")
        self.indent -= 1
        self.emit("def _go_copy(dst, src):")
        self.indent += 1
        self.emit("if _go_builtins.isinstance(src, _go_builtins.str): src = src.encode('latin-1' if _go_builtins.all(_go_builtins.ord(ch) <= 255 for ch in src) else 'utf-8')")
        self.emit("n = _go_builtins.min(_go_builtins.len(dst), _go_builtins.len(src)); dst[:n] = src[:n]; return n")
        self.indent -= 1
        self.emit("def _go_copy_slice(base, lo, hi, src):")
        self.indent += 1
        self.emit("if _go_builtins.isinstance(src, _go_builtins.str): src = src.encode('latin-1' if _go_builtins.all(_go_builtins.ord(ch) <= 255 for ch in src) else 'utf-8')")
        self.emit("start = 0 if lo is None else lo; end = _go_builtins.len(base) if hi is None else hi; n = _go_builtins.min(end - start, _go_builtins.len(src)); base[start:start+n] = src[:n]; return n")
        self.indent -= 1
        self.emit("def _go_append(seq, *values):")
        self.indent += 1
        self.emit("if _go_builtins.isinstance(seq, _go_builtins.tuple): seq = _go_builtins.list(seq)")
        self.emit("if _go_builtins.isinstance(seq, _go_builtins.bytes): seq = _go_builtins.bytearray(seq)")
        self.emit("seq.extend(values)")
        self.emit("return seq")
        self.indent -= 1
        self.emit("def _go_div(a, b):")
        self.indent += 1
        self.emit("if _go_builtins.isinstance(a, _go_builtins.int) and _go_builtins.isinstance(b, _go_builtins.int): return _go_builtins.int(a / b) if b else (_ for _ in ()).throw(_go_builtins.ZeroDivisionError())")
        self.emit("return a / b")
        self.indent -= 1
        self.emit("def _go_index(base, index):")
        self.indent += 1
        self.emit("if _go_builtins.isinstance(base, _go_builtins.str) and _go_builtins.isinstance(index, _go_builtins.int): return base.encode('utf-8')[index]")
        self.emit("return base[index]")
        self.indent -= 1
        self.emit("def _go_set_index(base, index, value):")
        self.indent += 1
        self.emit("if _go_builtins.isinstance(base, _go_builtins.bytearray): base[index] = value; return value")
        self.emit("base[index] = value; return value")
        self.indent -= 1
        self.emit("import builtins as _go_builtins")
        self.emit("def _go_string(x):")
        self.indent += 1
        self.emit("if isinstance(x, (_go_builtins.bytes, _go_builtins.bytearray)): return _go_builtins.bytes(x).decode('utf-8', 'replace')")
        self.emit("if _go_builtins.isinstance(x, (_go_builtins.list, _go_builtins.tuple)) and _go_builtins.all(_go_builtins.isinstance(v, _go_builtins.int) and 0 <= v <= 255 for v in x): return _go_builtins.bytes(x).decode('utf-8', 'replace')")
        self.emit("return _go_builtins.str(x)")
        self.indent -= 1
        self.emit("append = _go_append")
        self.emit("string = _go_builtins.str")
        self.emit("nil = None")
        self.emit("byte = _go_builtins.int")
        self.emit("rune = _go_builtins.int")
        self.emit("uint = _go_builtins.int; uint8 = _go_builtins.int; uint16 = _go_builtins.int; uint32 = _go_builtins.int; uint64 = _go_builtins.int")
        self.emit("int8 = _go_builtins.int; int16 = _go_builtins.int; int32 = _go_builtins.int; int64 = _go_builtins.int; uintptr = _go_builtins.int")
        self.emit("any = _go_builtins.object")
        self.emit("comparable = _go_builtins.object")
        self.emit("def _go_deref(value):")
        self.indent += 1
        self.emit("if _go_builtins.hasattr(value, 'get') and _go_builtins.callable(value.get): return value.get()")
        self.emit("if _go_builtins.isinstance(value, _go_builtins.dict) and 'value' in value: return value['value']")
        self.emit("return value")
        self.indent -= 1
        self.emit("def _go_struct(**fields):")
        self.indent += 1
        self.emit("obj = _go_builtins.type('GoStruct', (), {})()")
        self.emit("for k, v in fields.items(): _go_builtins.setattr(obj, k, v)")
        self.emit("return obj")
        self.indent -= 1
        self.emit("def _go_store_deref(pointer, value):")
        self.indent += 1
        self.emit("if _go_builtins.hasattr(pointer, 'set') and _go_builtins.callable(pointer.set): pointer.set(value); return value")
        self.emit("if _go_builtins.isinstance(pointer, _go_builtins.dict) and 'value' in pointer: pointer['value'] = value; return value")
        self.emit("return value")
        self.indent -= 1
        self.emit()
        if tree.imports:
            self.emit("from go_lower import load_go_package as __go_load_package")
        self.emit()
        if self._needs:
            imports = []
            if "runtime" in self._needs:
                imports.append("import goruntime as _go_runtime")
            if "goto" in self._needs:
                # Goto is a lowering-level control-flow primitive; keep it
                # self-contained instead of depending on a separate Python
                # module that may not be present when translating the Go
                # standard library.
                self.emit("class _GoGoto(Exception): pass")
                self.emit("_go_runtime_goto = _GoGoto")
            for imp in imports:
                self.emit(imp)
            self.emit()

        self.emit(f"__go_package__ = {tree.package!r}")
        self.emit("__go_imports__ = {}")
        self.emit(f"__go_import_paths__ = {self.import_paths!r}")
        if any(isinstance(n, ForStmt) and n.range_expr is not None for n in self._walk(tree)):
            self.emit("def _go_range(x):")
            self.indent += 1
            self.emit("return x.items() if isinstance(x, dict) else enumerate(x)")
            self.indent -= 1
            self.emit()
        for imp in tree.imports:
            self.lower_import(imp)
        if tree.imports:
            self.emit()
        # Go declarations are order-independent.  Emit type declarations
        # first so constants/variables may safely use a type that appears
        # later in the source (e.g. runtime's hchanSize uses hchan()).
        type_decls = []
        other_decls = []
        for decl in tree.declarations:
            items = decl if isinstance(decl, list) else [decl]
            type_decls.extend(d for d in items if isinstance(d, TypeSpec))
            rest = [d for d in items if not isinstance(d, TypeSpec)]
            if rest:
                # Preserve grouped const declarations so iota continues to
                # advance within the original const group.
                other_decls.append(rest if isinstance(decl, list) else rest[0])
        ordered_decls = type_decls + other_decls
        self._top_level_decls = [d for decl in ordered_decls for d in (decl if isinstance(decl, list) else [decl])]
        for decl in ordered_decls:
            if isinstance(decl, list):
                const_group = bool(decl) and all(isinstance(d, ConstSpec) for d in decl)
                if const_group:
                    self.iota = 0
                    self._last_const_values = None
                for d in decl:
                    self.lower_decl(d)
                    if const_group:
                        self.iota += 1
            else:
                if isinstance(decl, ConstSpec):
                    self.iota = 0
                    self._last_const_values = None
                    self.lower_decl(decl)
                else:
                    self.lower_decl(decl)
        # Methods are emitted as normal Python functions first.  Bind them to
        # their receiver classes after all declarations have been lowered so
        # source order does not matter (Go methods may appear before/after the
        # receiver type declaration).
        for receiver_type, method_name, emitted_name in self._method_bindings:
            self.emit(f"{py_ident(receiver_type)}.{py_ident(method_name)} = {py_ident(emitted_name)}")
        return "\n".join(self.lines) + "\n"

    def _import_binding(self, imp: Import) -> str:
        path = imp.path
        default_name = path.rsplit("/", 1)[-1]
        return (
            self.runtime_bindings.get(path)
            or self.runtime_bindings.get(imp.name or "")
            or self.runtime_bindings.get(default_name)
            or path
        )

    def _import_package_name(self, imp: Import) -> str:
        # An unaliased Go import is bound using the imported package's declared
        # package name, not the final component of its import path.  These can
        # differ substantially (github.com/docker/go-units -> package units),
        # and the latter can even be an invalid Python identifier.
        if imp.name and imp.name not in ("_", "."):
            return py_ident(imp.name)
        if imp.name == ".":
            return py_ident(imp.path.rsplit("/", 1)[-1])
        declared = _go_disk_package_name(imp.path, self.import_paths)
        return py_ident(declared or imp.path.rsplit("/", 1)[-1])

    def lower_import(self, imp: Import) -> None:
        """Resolve Go imports through the filesystem-backed package loader."""
        path = imp.path
        binding = self._import_binding(imp)
        name = imp.name

        if name == "_":
            self.emit(f"__go_load_package({binding!r}, __go_imports__, search_paths=__go_import_paths__)")
            return

        package_name = self._import_package_name(imp)
        self.emit(f"{package_name} = __go_load_package({binding!r}, __go_imports__, search_paths=__go_import_paths__)")
        if name == ".":
            self.emit(
                f"globals().update({{k: v for k, v in {package_name}.items() if not k.startswith('_')}})"
            )
        else:
            self.emit(f"__go_imports__[{package_name!r}] = {package_name}")

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
                    params.append(py_ident(n) if n != "_" else f"arg{len(params)}")
        for f in d.params:
            names = f.names or [f"arg{len(params)}"]
            for n in names:
                name = py_ident(n) if n != "_" else f"arg{len(params)}"
                if isinstance(f.type_expr, Expr) and f.type_expr.kind == "variadic":
                    params.append("*" + name)
                else:
                    params.append(name)
        emitted_name = py_ident(d.name)
        if receiver:
            # Methods live in Go's method namespace and therefore do not
            # collide with package-level types/functions.  Python has one
            # module namespace, so give translated methods private unique
            # names and bind them to the receiver class below.
            receiver_name = self._receiver_type_name(receiver[0].type_expr) or "receiver"
            emitted_name = f"__go_method_{py_ident(receiver_name)}_{py_ident(d.name)}"
        self.emit(f"def {emitted_name}({', '.join(params)}):")
        self.indent += 1
        if self._package_names:
            param_names = {p.lstrip("*") for p in params}
            globals_needed = [py_ident(n) for n in sorted(self._package_names) if py_ident(n) not in param_names]
            if globals_needed:
                self.emit("global " + ", ".join(globals_needed))
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
        if receiver:
            receiver_type = self._receiver_type_name(receiver[0].type_expr)
            if receiver_type:
                self._method_bindings.append((receiver_type, d.name, emitted_name))
                # Keep a package-level alias for translated methods when there
                # is no package-level function with the same name.  This keeps
                # compatibility with the existing generated-code API, where
                # callers may invoke Start(Daemon(...)) directly, while the
                # receiver binding below still makes Daemon(...).Start() work.
                # Do not export a method into the package namespace when its
                # name is a Go predeclared identifier.  In Go, a method named
                # `make`, `len`, `cap`, etc. does not shadow the builtin in
                # ordinary package-level expressions.  Doing that in Python
                # would overwrite our runtime builtin and corrupt unrelated
                # expressions (for example math/big's nat.make vs make(...)).
                if d.name not in _GO_PREDECLARED and not any(
                    existing is not d
                    and getattr(existing, "name", None) == d.name
                    and getattr(existing, "receiver", None) is None
                    for existing in self._top_level_decls
                ):
                    self.emit(f'{py_ident(d.name)} = {py_ident(emitted_name)}')

    def _receiver_type_name(self, type_expr: Any) -> Optional[str]:
        # Receiver types are commonly `T` or `*T`; unwrap the pointer node.
        if isinstance(type_expr, Expr):
            if type_expr.kind == "type_name":
                return str(type_expr.value)
            if type_expr.kind in ("pointer", "paren") and type_expr.children:
                return self._receiver_type_name(type_expr.children[0])
            if type_expr.children:
                for child in type_expr.children:
                    found = self._receiver_type_name(child)
                    if found:
                        return found
        return None

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
            # Blank fields (`_`) carry compile-time layout information in Go
            # but have no runtime selector.  Repeated blank fields are legal
            # in Go and cannot become duplicate Python parameters.
            fields = []
            field_types = {}
            embedded = []
            for f in t.fields:
                names = list(f.names)
                if not names and isinstance(f.type_expr, Expr) and f.type_expr.kind == "type_name":
                    names = [str(f.type_expr.value).split(".")[-1]]
                    embedded.append(names[0])
                for n in names:
                    if n != "_" and n not in fields:
                        fields.append(n)
                        field_types[n] = f.type_expr
            if embedded:
                self.emit("def __getattr__(self, name):")
                self.indent += 1
                for n in embedded:
                    self.emit(f"base = object.__getattribute__(self, {py_ident(n)!r})")
                    self.emit("if hasattr(base, name): return getattr(base, name)")
                self.emit("raise AttributeError(name)")
                self.indent -= 1
            if fields:
                def _ctor_name(n: str) -> str:
                    # A Go field may legally be named `self`; it cannot be
                    # used as a Python constructor parameter because `self`
                    # is already the implicit instance parameter.
                    return "__go_self_field" if py_ident(n) == "self" else py_ident(n)
                self.emit("def __init__(self, " + ", ".join(_ctor_name(x) + "=None" for x in fields) + "):")
                self.indent += 1
                for n in fields:
                    z = self._zero_value_expr(field_types.get(n))
                    self.emit(f"self.{py_ident(n)} = {_ctor_name(n)} if {_ctor_name(n)} is not None else {z}")
                self.indent -= 1
            else:
                self.emit("pass")
            self.indent -= 1
        elif isinstance(t, Expr) and t.kind == "slice":
            # Named Go slice types need to retain their concrete type across
            # Python slicing.  list.__getitem__ normally returns a plain list,
            # which would silently discard methods such as fmt.buffer.writeString.
            self.emit(f"class {py_ident(d.name)}(list):")
            self.indent += 1
            self.emit("def __init__(self, *values):")
            self.indent += 1
            self.emit("if len(values) == 1 and isinstance(values[0], (list, tuple)): values = tuple(values[0])")
            self.emit("super().__init__(values)")
            self.indent -= 1
            self.emit("def __getitem__(self, key):")
            self.indent += 1
            self.emit("value = super().__getitem__(key)")
            self.emit("return type(self)(value) if isinstance(key, slice) else value")
            self.indent -= 1
            self.indent -= 1
        elif isinstance(t, Expr) and t.kind == "array":
            # A named Go array is a distinct, fixed-length value type.  Python
            # list subclasses are sufficient for the current lowering, but a
            # zero-value array must still contain its declared number of zero
            # elements; an empty list changes the semantics of expressions
            # such as `var t [256]uint32` followed by indexed assignment.
            self.emit(f"class {py_ident(d.name)}(list):")
            self.indent += 1
            array_len = None
            if isinstance(t.value, Expr) and t.value.kind == "literal":
                try:
                    array_len = int(str(t.value.value), 0)
                except (TypeError, ValueError):
                    array_len = None
            self.emit("def __init__(self, *values):")
            self.indent += 1
            self.emit("if len(values) == 1 and isinstance(values[0], (list, tuple)): values = tuple(values[0])")
            if array_len is not None:
                self.emit(f"_n = {array_len}")
                self.emit("_vals = list(values)")
                self.emit("if len(_vals) < _n: _vals.extend([0] * (_n - len(_vals)))")
                self.emit("elif len(_vals) > _n: _vals = _vals[:_n]")
                self.emit("super().__init__(_vals)")
            else:
                self.emit("super().__init__(values)")
            self.indent -= 1
            self.emit("def __getitem__(self, key):")
            self.indent += 1
            self.emit("value = super().__getitem__(key)")
            self.emit("return type(self)(value) if isinstance(key, slice) else value")
            self.indent -= 1
            self.indent -= 1
        elif isinstance(t, Expr) and t.kind == "func_type":
            # Named Go function types are callable values and can also have
            # methods.  Represent them as a tiny callable wrapper instead of
            # collapsing them to Python's immutable `object`.
            self.emit(f"class {py_ident(d.name)}:")
            self.indent += 1
            self.emit("def __init__(self, fn=None):")
            self.indent += 1
            self.emit("self._fn = fn")
            self.indent -= 1
            self.emit("def __call__(self, *args, **kwargs):")
            self.indent += 1
            self.emit("if self._fn is None: raise TypeError('nil Go function value')")
            self.emit("return self._fn(*args, **kwargs)")
            self.indent -= 1
            self.indent -= 1
        elif isinstance(t, InterfaceType):
            self.emit(f"class {py_ident(d.name)}:")
            self.indent += 1
            if t.embeds:
                self.emit("# embedded interfaces: " + ", ".join(self.expr(x) for x in t.embeds))
            for m in t.methods:
                params = []
                for f in m.params:
                    names = f.names or [f"arg{len(params)}"]
                    for n in names:
                        params.append(py_ident(n))
                self.emit(f"def {py_ident(m.name)}({', '.join(['self'] + params)}):")
                self.indent += 1
                self.emit("raise NotImplementedError")
                self.indent -= 1
            if not t.methods:
                self.emit("pass")
            self.indent -= 1
        else:
            # A Go defined type is distinct from its underlying type and may
            # have methods.  Python builtins such as int/str cannot accept
            # attributes, so named scalar types are represented by lightweight
            # subclasses.  This is important for stdlib types such as
            # runtime.lfstack, which define methods on an integer-backed type.
            if isinstance(t, Expr) and t.kind == "type_name":
                base = {
                    "bool": "int", "byte": "int", "rune": "int",
                    "int": "int", "int8": "int", "int16": "int",
                    "int32": "int", "int64": "int",
                    "uint": "int", "uint8": "int", "uint16": "int",
                    "uint32": "int", "uint64": "int", "uintptr": "int",
                    "float32": "float", "float64": "float",
                    "complex64": "complex", "complex128": "complex",
                    "string": "str",
                }.get(str(t.value))
                if base:
                    self.emit(f"class {py_ident(d.name)}({base}):")
                    self.indent += 1
                    self.emit("pass")
                    self.indent -= 1
                    return
            if isinstance(t, Expr) and t.kind == "map":
                self.emit(f"class {py_ident(d.name)}(dict):")
                self.indent += 1; self.emit("pass"); self.indent -= 1
                return
            # Preserve the existing callable representation for aliases and
            # less common underlying types that do not need Python methods.
            self.emit(f"{py_ident(d.name)} = {self.type_expr(t)}")

    def _zero_value_expr(self, type_expr: Any) -> str:
        """Lower Go's zero value for declarations without an initializer."""
        if isinstance(type_expr, StructType):
            fields = []
            for f in type_expr.fields:
                for n in f.names:
                    if n != "_":
                        fields.append(f"{py_ident(n)}=None")
            return "_go_struct(" + ", ".join(fields) + ")"
        if isinstance(type_expr, Expr):
            if type_expr.kind == "type_name":
                name = str(type_expr.value)
                if "." in name:
                    return f"{py_ident(name.split('.', 1)[0])}.{py_ident(name.split('.', 1)[1])}()"
                return {
                    "bool": "False",
                    "string": "''",
                    "byte": "0", "rune": "0",
                    "int": "0", "int8": "0", "int16": "0", "int32": "0", "int64": "0",
                    "uint": "0", "uint8": "0", "uint16": "0", "uint32": "0", "uint64": "0",
                    "uintptr": "0", "float32": "0.0", "float64": "0.0",
                    "complex64": "0j", "complex128": "0j",
                }.get(name, f"globals()[{py_ident(name)!r}]()")
            if type_expr.kind == "pointer":
                return "None"
            if type_expr.kind == "selector":
                return f"{self.type_expr(type_expr)}()"
            if type_expr.kind == "name":
                return f"{self.type_expr(type_expr)}()"
            if type_expr.kind == "array":
                length = type_expr.value
                if isinstance(length, Expr):
                    return f"[None] * int({self.expr(length)})"
                return "[]"
            if type_expr.kind == "map":
                return "{}"
        return "None"

    def lower_var(self, d: VarSpec) -> None:
        vals = [self.expr(x) for x in d.values]
        if not vals:
            vals = [self._zero_value_expr(d.type_expr)] * len(d.names)
        if len(d.names) == 1:
            self.emit(f"{py_ident(d.names[0])} = {vals[0]}")
        else:
            rhs = ", ".join(vals)
            self.emit(f"{', '.join(py_ident(n) for n in d.names)} = {rhs}")

    def lower_const(self, d: ConstSpec) -> None:
        values = d.values if d.values else (self._last_const_values or [])
        self.lower_var(VarSpec(d.line, d.names, d.type_expr, values))
        if values:
            self._last_const_values = values

    def lower_block(self, b: Block) -> None:
        if not b.statements:
            self.emit("pass")
            return
        for s in b.statements:
            self.lower_stmt(s)

    def lower_stmt(self, s: Any) -> None:
        if isinstance(s, list):
            for item in s:
                self.lower_stmt(item)
        elif isinstance(s, Block):
            self.lower_block(s)
        elif isinstance(s, (VarSpec, ConstSpec)):
            self.lower_var(s)
        elif isinstance(s, SimpleStmt):
            self.lower_simple(s)
        elif isinstance(s, IfStmt):
            # Go permits a short/simple statement before the condition:
            # `if x := f(); x > 0 { ... }`.  Python has no equivalent
            # semicolon-bearing `if` header, so lower the initializer just
            # before the `if`.  Its scope is intentionally a little wider
            # than Go's block scope, but the generated semantics inside the
            # condition/body are preserved.
            if s.init is not None:
                self.lower_simple(s.init)
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
            self.emit(f"_go_runtime.defer(lambda: ({self.expr(s.call)}))")
        elif isinstance(s, GoStmt):
            self.emit(f"_go_runtime.go(lambda: ({self.expr(s.call)}))")
        elif isinstance(s, BranchStmt):
            if s.keyword == "goto":
                self.emit(f"raise _go_runtime_goto({s.label!r})")
            elif s.keyword == "fallthrough":
                self.emit("# Go fallthrough")
            else:
                if self._select_callback and s.keyword in ("break", "continue"):
                    self.emit(f"return _go_select_{s.keyword}")
                else:
                    self.emit(s.keyword)
        elif isinstance(s, LabelStmt):
            # Labels are control-flow markers, not Python nested functions.
            # Lower the labeled statement in-place so Go `break`/`continue`
            # remain in the enclosing Python loop instead of becoming illegal
            # control statements inside a generated helper function.  Goto
            # transfer itself remains handled by the existing goto lowering.
            self.emit(f"# Go label: {s.label}")
            self.lower_stmt(s.statement)
        elif isinstance(s, Expr):
            self.emit(self.expr(s))
        elif isinstance(s, (TypeSpec, VarSpec, ConstSpec)):
            # Local type/var/const declarations inside function bodies.
            self.lower_decl(s)
        elif isinstance(s, list):
            # Grouped var/const/type declarations return a list of specs.
            for item in s:
                self.lower_stmt(item)
        else:
            raise LoweringError(f"unsupported statement: {type(s).__name__}")

    def lower_simple(self, s: SimpleStmt) -> None:
        if s.op in ("++", "--"):
            op = "+=" if s.op == "++" else "-="
            target = s.left[0]
            if isinstance(target, Expr) and target.kind == "index":
                base = self.expr(target.children[0])
                index = self.expr(target.children[1])
                self.emit(f"_go_set_index({base}, {index}, _go_index({base}, {index}) {op[:-1]} 1)")
            else:
                self.emit(f"{self.expr(target)} {op} 1")
            return
        # Go dereference expressions are assignable lvalues. Python cannot
        # assign to a call expression such as ``Optional[T](p)``, so lower
        # ``*p = v`` through the runtime store primitive instead.
        if len(s.left) == 1 and isinstance(s.left[0], Expr) and s.left[0].kind == "unary" and s.left[0].value == "*":
            target = self.expr(s.left[0].children[0])
            if s.op == "=":
                self.emit(f"_go_store_deref({target}, {self.expr(s.right[0])})")
                return
            if s.op in ("+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "&^="):
                rhs = self.expr(s.right[0])
                pyop = "&=" if s.op == "&^=" else s.op
                if s.op == "&^=":
                    value = f"_go_deref({target}) & ~({rhs})"
                else:
                    value = f"_go_deref({target}) {pyop[:-1]} {rhs}"
                self.emit(f"_go_store_deref({target}, {value})")
                return
        # Go two-value type assertion: x, ok := expr.(T)
        # Lower to: x = expr; ok = <duck-type check>
        if s.op in (":=", "=") and len(s.left) == 2 and len(s.right) == 1:
            rhs = s.right[0]
            if isinstance(rhs, Expr) and rhs.kind == "type_assert" and rhs.value != "type":
                subject = self.expr(rhs.children[0])
                lv = self.expr(s.left[0])
                ok_v = self.expr(s.left[1])
                # Build the check against the stable temporary directly.
                # String replacement of the original subject is unsafe: a
                # subject such as `n` also occurs inside literals/identifiers
                # such as `None`, producing malformed Python.
                self.emit(f"__go_ta_subj = {subject}")
                self.emit(f"{lv} = __go_ta_subj")
                check = self._interface_check(rhs.value, "__go_ta_subj")
                self.emit(f"{ok_v} = {check}")
                return
        # Parallel assignments to indexed Go values (notably runtime
        # scheduler queue swaps) cannot use Python tuple assignment because
        # reads are lowered through _go_index().  Evaluate all RHS values
        # first, then write them back in Go's parallel-assignment order.
        if (len(s.left) > 1 and all(isinstance(v, Expr) and v.kind == "index" for v in s.left)
                and len(s.left) == len(s.right) and s.op in ("=", ":=")):
            self.emit("__go_parallel_rhs = (" + ", ".join(self.expr(v) for v in s.right) + ",)")
            for n, target in enumerate(s.left):
                base = self.expr(target.children[0])
                index = self.expr(target.children[1])
                self.emit(f"_go_set_index({base}, {index}, __go_parallel_rhs[{n}])")
            return
        # Index expressions are not valid Python lvalues once reads are
        # routed through _go_index().  Keep assignment semantics explicit.
        if any(isinstance(target, Expr) and target.kind == "index" for target in s.left):
            if len(s.left) > 1 and s.op in ("=", ":="):
                self.emit("__go_assign_values = (" + ", ".join(self.expr(x) for x in s.right) + (",)" if len(s.right) == 1 else ")"))
                for idx, target in enumerate(s.left):
                    value = f"__go_assign_values[{idx}]"
                    if isinstance(target, Expr) and target.kind == "index":
                        self.emit(f"_go_set_index({self.expr(target.children[0])}, {self.expr(target.children[1])}, {value})")
                    else:
                        self.emit(f"{self.expr(target)} = {value}")
                return
        if len(s.left) == 1 and isinstance(s.left[0], Expr) and s.left[0].kind == "index":
            target = s.left[0]
            base = self.expr(target.children[0])
            index = self.expr(target.children[1])
            rhs = self.expr(s.right[0])
            if s.op in ("=", ":="):
                self.emit(f"_go_set_index({base}, {index}, {rhs})")
                return
            if s.op == "&^=":
                self.emit(f"_go_set_index({base}, {index}, _go_index({base}, {index}) & ~({rhs}))")
                return
            if s.op in ("+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="):
                self.emit(f"_go_set_index({base}, {index}, _go_index({base}, {index}) {s.op[:-1]} {rhs})")
                return
        left = ", ".join(self.expr(x) for x in s.left)
        if s.op == "<-":
            self.emit(f"{self.expr(s.left[0])}.send({self.expr(s.right[0])})")
        else:
            if s.op == ":=":
                op = "="
                self.emit(f"{left} {op} " + ", ".join(self.expr(x) for x in s.right))
            elif s.op == "&^=":
                # Go bit-clear assignment: x &^= y == x &= ^y.
                self.emit(f"{left} &= ~(" + ", ".join(self.expr(x) for x in s.right) + ")")
            else:
                self.emit(f"{left} {s.op} " + ", ".join(self.expr(x) for x in s.right))

    def _interface_check(self, type_expr: Any, subject: str) -> str:
        """Return a Python boolean expression that checks whether *subject*
        satisfies the Go interface / named type *type_expr*.

        For interface types we use duck-typing (hasattr checks on each method).
        For named types we use isinstance where possible.
        """
        if isinstance(type_expr, InterfaceType):
            if not type_expr.methods:
                # interface{} / any — everything satisfies it
                return "True"
            checks = [f"hasattr({subject}, {py_ident(m.name)!r})" for m in type_expr.methods]
            return " and ".join(checks)
        if isinstance(type_expr, Expr):
            if type_expr.kind in ("type_name", "name"):
                name = py_ident(str(type_expr.value))
                if name in ("interface", "any", "object"):
                    return "True"
                return f"isinstance({subject}, {name})"
            if type_expr.kind == "pointer":
                # *T — we don't model pointer types, treat as truthy
                return f"({subject} is not None)"
        # Fallback: can't determine statically, assume True
        return "True"

    def lower_for(self, s: ForStmt) -> None:
        if s.range_expr is not None:
            names = [py_ident(x.value) if isinstance(x, Expr) and x.kind == "name" else py_ident(str(x)) for x in s.range_names]
            target = ", ".join(names) or "_"
            source = self.expr(s.range_expr)
            if len(names) >= 2:
                self.emit(f"for {names[0]}, {names[1]} in _go_range({source}):")
            else:
                self.emit(f"for {target} in {source}:")
            self.indent += 1
            self._loop_depth += 1
            self._break_depth += 1
            self.lower_block(s.body)
            self._break_depth -= 1
            self._loop_depth -= 1
            self.indent -= 1
            return
        if s.init is not None and s.cond is not None and s.post is not None:
            self._lower_for_clause(s.init)
            self.emit(f"while {self.expr(s.cond)}:")
            self.indent += 1
            self._loop_depth += 1
            self.lower_block(s.body)
            self._lower_for_clause(s.post)
            self._loop_depth -= 1
            self.indent -= 1
        elif s.cond is not None:
            self.emit(f"while {self.expr(s.cond)}:")
            self.indent += 1
            self._loop_depth += 1
            self._break_depth += 1
            self.lower_block(s.body)
            self._break_depth -= 1
            self._loop_depth -= 1
            self.indent -= 1
        else:
            self.emit("while True:")
            self.indent += 1
            self._loop_depth += 1
            self._break_depth += 1
            self.lower_block(s.body)
            self._break_depth -= 1
            self._loop_depth -= 1
            self.indent -= 1

    def _lower_for_clause(self, s) -> None:
        """Lower a for-loop init or post clause which may be a SimpleStmt or
        an arbitrary expression (e.g. an immediately-called func literal)."""
        if isinstance(s, SimpleStmt):
            self.lower_simple(s)
        elif isinstance(s, Expr):
            self.emit(self.expr(s))
        else:
            self.lower_stmt(s)

    def lower_switch(self, s: SwitchStmt) -> None:
        # Lower Go's first-match switch semantics to an if/elif chain wrapped
        # in a `while True: ... break` so that `break` statements inside
        # cases correctly exit the switch (as in Go semantics).

        # Detect a type switch: `switch x := expr.(type)` or `switch expr.(type)`
        # The parser stores the whole thing in s.tag as a SimpleStmt (for the
        # init form) or directly as a type_assert Expr.
        is_type_switch = False
        ts_subject = None   # Python expression for the value being switched on
        ts_var = None       # Python name to bind the matched value to (or "_")

        if isinstance(s.tag, SimpleStmt) and s.tag.op == ":=" and len(s.tag.right) == 1:
            rhs = s.tag.right[0]
            if isinstance(rhs, Expr) and rhs.kind == "type_assert" and rhs.value == "type":
                is_type_switch = True
                ts_subject = self.expr(rhs.children[0])
                ts_var = self.expr(s.tag.left[0]) if s.tag.left else "_"
        elif isinstance(s.tag, Expr) and s.tag.kind == "type_assert" and s.tag.value == "type":
            is_type_switch = True
            ts_subject = self.expr(s.tag.children[0])
            ts_var = "_"

        if is_type_switch:
            self._lower_type_switch(s, ts_subject, ts_var)
            return

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
            if stmts:
                self.lower_block(Block(c.line, stmts))
            else:
                self.emit("pass")
            if fall and index + 1 < len(clauses):
                emit_case_body(index + 1)

        self.emit("while True:")
        self.indent += 1
        self._break_depth += 1
        first = True
        for i, c in enumerate(clauses):
            cond = "True" if c.default else " or ".join(f"{tag} == {self.expr(x)}" for x in c.expressions)
            self.emit(("if " if first else "elif ") + cond + ":")
            self.indent += 1
            emit_case_body(i)
            self.emit("break")
            self.indent -= 1
            first = False
        if first:
            # Empty switch — still need the while body
            self.emit("pass")
        self.emit("break")
        self._break_depth -= 1
        self.indent -= 1

    def _lower_type_switch(self, s: SwitchStmt, subject: str, var: str) -> None:
        """Lower a Go type-switch to a Python if/elif chain using duck-typing."""
        # Evaluate subject once
        self.emit(f"__go_ts_val = {subject}")
        clauses = s.clauses

        def emit_body(index: int) -> None:
            c = clauses[index]
            # Bind the type-switch variable to the subject value.
            if var and var != "_":
                self.emit(f"{var} = __go_ts_val")
            stmts = list(c.statements)
            if stmts:
                self.lower_block(Block(c.line, stmts))
            else:
                self.emit("pass")

        self.emit("while True:")
        self.indent += 1
        self._break_depth += 1
        first = True
        for i, c in enumerate(clauses):
            if c.default:
                kw = "if " if first else "elif "
                self.emit(kw + "True:")
            else:
                # Each case expression is a type; build a duck-type check.
                parts = []
                for type_expr in c.expressions:
                    parts.append(self._interface_check(type_expr, "__go_ts_val"))
                cond = " or ".join(parts) if parts else "True"
                kw = "if " if first else "elif "
                self.emit(kw + cond + ":")
            self.indent += 1
            emit_body(i)
            self.emit("break")
            self.indent -= 1
            first = False
        if first:
            self.emit("pass")
        self.emit("break")
        self._break_depth -= 1
        self.indent -= 1

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
            # A receive-only select case such as `case <-ch:` is represented
            # by the parser as the unary receive expression itself, rather than
            # a SimpleStmt.  It is still a valid communication clause.
            if isinstance(comm, Expr) and comm.kind == "unary" and comm.value == "<-":
                ch = self.expr(comm.children[0])
                self.emit(f"def {fn}(__go_value=None):")
                self.indent += 1
                self.emit("nonlocal __go_result")
                old_mode = self._select_callback; self._select_callback = True
                self.lower_block(Block(c.line, c.statements))
                self._select_callback = old_mode
                if not c.statements: self.emit("pass")
                self.indent -= 1
                self.emit(f"_go_select_cases.append(_go_runtime.case_recv({ch}, {fn}))")
                continue
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
        self.emit("__go_select_control = _go_runtime.select(*_go_select_cases)")
        self.emit("del _go_select_cases")
        # A select case is lowered as a Python callback.  break/continue
        # selected inside that callback cannot be emitted literally there;
        # the callback returns a control sentinel and the enclosing select
        # statement performs the actual branch.  This also makes nested
        # selects propagate control outward instead of producing illegal
        # `continue`/`break` statements inside generated callbacks.
        if self._select_callback:
            self.emit("if __go_select_control is _go_select_break or __go_select_control is _go_select_continue:")
            self.indent += 1
            self.emit("return __go_select_control")
            self.indent -= 1
        else:
            if self._loop_depth > 0:
                self.emit("if __go_select_control is _go_select_continue:")
                self.indent += 1
                self.emit("continue")
                self.indent -= 1
            if self._break_depth > 0:
                self.emit("if __go_select_control is _go_select_break:")
                self.indent += 1
                self.emit("break")
                self.indent -= 1

    def expr(self, x: Any) -> str:
        if isinstance(x, Expr):
            k = x.kind
            if k == "name":
                if x.value == "nil": return "None"
                if x.value == "true": return "True"
                if x.value == "false": return "False"
                if x.value == "iota": return str(self.iota)
                return py_ident(str(x.value))
            if k == "literal": return self.literal(str(x.value))
            if k == "type_name": return py_ident(str(x.value))
            if k == "variadic": return "*" + self.expr(x.children[0])
            if k == "binary":
                # Go's internal/goarch defines PtrSize as:
                #   4 << (^uintptr(0) >> 63)
                # This is an ideal constant whose value depends on the target
                # word size.  Do not let Python evaluate the expression using
                # its unbounded signed integers; materialize the Go constant.
                if x.value == "<<" and len(x.children) == 2:
                    left, right = x.children
                    if (isinstance(left, Expr) and left.kind == "literal"
                            and str(left.value) in {"4", "32"}
                            and isinstance(right, Expr) and right.kind == "binary"
                            and right.value == ">>"
                            and isinstance(right.children[1], Expr)
                            and right.children[1].kind == "literal"
                            and str(right.children[1].value) == "63"):
                        unary = right.children[0]
                        if (isinstance(unary, Expr) and unary.kind == "unary"
                                and unary.value == "^" and unary.children
                                and isinstance(unary.children[0], Expr)
                                and unary.children[0].kind == "call"
                                and len(unary.children[0].children) == 2
                                and isinstance(unary.children[0].children[0], Expr)
                                and str(unary.children[0].children[0].value) in {"uintptr", "uint"}
                                and isinstance(unary.children[0].children[1], Expr)
                                and str(unary.children[0].children[1].value) == "0"):
                            return "8 if __go_runtime_ptr_size__ == 8 else 4" if str(left.value) == "4" else "64 if __go_runtime_ptr_size__ == 8 else 32"
                op = BIN_OP.get(x.value, x.value)
                if x.value == "/":
                    return f"_go_div({self.expr(x.children[0])}, {self.expr(x.children[1])})"
                return f"({self.expr(x.children[0])} {op} {self.expr(x.children[1])})"
            if k == "unary":
                op = UNARY_OP.get(x.value, x.value)
                if x.value == "<-": return f"{self.expr(x.children[0])}.recv()"
                if x.value in ("&", "*"): return self.expr(x.children[0])
                # Go's unary ^ is a bitwise complement whose width depends on
                # the operand's integer type.  Python integers are unbounded,
                # so translating ^uintptr(0) directly to ~uintptr(0) produces
                # -1 and expressions such as `4 << (^uintptr(0) >> 63)` then
                # fail with Python's negative-shift error.  Preserve the Go
                # constant semantics for the architecture-sized uintptr case.
                if x.value == "^":
                    operand = x.children[0]
                    if (isinstance(operand, Expr) and operand.kind == "call"
                            and len(operand.children) == 2
                            and isinstance(operand.children[0], Expr)
                            and operand.children[0].kind in ("name", "type_name")
                            and str(operand.children[0].value) == "uintptr"
                            and isinstance(operand.children[1], Expr)
                            and operand.children[1].kind == "literal"
                            and str(operand.children[1].value) == "0"):
                        return "((1 << (8 * __go_runtime_ptr_size__)) - 1)"
                return f"({op}{self.expr(x.children[0])})"
            if k == "func_lit":
                params=[]
                for f in x.children[0]:
                    params.extend(py_ident(n) for n in (f.names or [f"arg{len(params)}"]))
                body=x.children[2]
                if getattr(body, "statements", None) and len(body.statements)==1 and isinstance(body.statements[0], ReturnStmt):
                    vals=body.statements[0].values
                    ret="None" if not vals else self.expr(vals[0]) if len(vals)==1 else "(" + ", ".join(self.expr(v) for v in vals) + ")"
                    return f"lambda {', '.join(params)}: {ret}"
                return "lambda *args, **kwargs: None"
            if k == "slice":
                base=self.expr(x.children[0]); lo=self.expr(x.children[1]) if x.children[1] is not None else ""; hi=self.expr(x.children[2]) if x.children[2] is not None else ""
                if x.children[3] is not None:
                    return f"{base}[{lo}:{hi}:{self.expr(x.children[3])}]"
                return f"{base}[{lo}:{hi}]"
            if k == "type_assert":
                # Preserve the value for ordinary assertions.  The two-value
                # form is handled by assignment lowering when its result is
                # destructured.
                return self.expr(x.children[0])
            if k == "keyed": return f"({self.expr(x.children[0])}, {self.expr(x.children[1])})"
            if k == "call":
                callee = x.children[0]
                # Go type conversions may use pointer-to-type syntax, e.g.
                # (*error)(nil).  The translator does not model Go's static
                # type objects, so lower this form as the underlying value.
                if (isinstance(callee, Expr) and callee.kind in ("unary", "pointer")
                        and callee.children and (callee.kind == "pointer" or callee.value == "*") ):
                    # Pointer type conversion, e.g. (*unsafe.Pointer)(p).
                    # The static type is not represented by the Python backend;
                    # preserve the underlying address/reference value.
                    return self.expr(x.children[1]) if len(x.children) == 2 else "None"
                raw_args = x.children[1:]
                if isinstance(callee, Expr) and callee.kind == "name":
                    builtin = {
                        "make": "_go_make",
                        "len": "_go_len",
                        "cap": "_go_cap",
                        "copy": "_go_copy",
                        "append": "_go_append",
                    }.get(callee.value)
                    if callee.value == "copy" and raw_args and isinstance(raw_args[0], Expr) and raw_args[0].kind == "slice":
                        sl = raw_args[0]
                        lo = self.expr(sl.children[1]) if sl.children[1] is not None else "None"
                        hi = self.expr(sl.children[2]) if sl.children[2] is not None else "None"
                        src = self.expr(raw_args[1]) if len(raw_args) > 1 else "[]"
                        return f"_go_copy_slice({self.expr(sl.children[0])}, {lo}, {hi}, {src})"
                    if builtin:
                        args = ", ".join(self.expr(a) for a in raw_args)
                        return f"{builtin}({args})"
                if isinstance(callee, Expr) and callee.kind == "array":
                    if raw_args and isinstance(raw_args[0], Expr) and raw_args[0].kind == "name" and raw_args[0].value == "nil":
                        return "[]"
                    if len(raw_args) == 1:
                        return f"_go_builtins.list({self.expr(raw_args[0])})"
                    return "[]"
                fn = self.expr(callee)
                # A function literal used as a callee must be parenthesized.
                # Without this, `func() {}()` lowers to `lambda: None()`;
                # Python parses the call as part of the lambda body and emits
                # a SyntaxWarning (and changes the call semantics).
                if isinstance(callee, Expr) and callee.kind == "func_lit":
                    fn = f"({fn})"
                if isinstance(callee, Expr) and callee.kind == "name" and callee.value == "string":
                    fn = "_go_string"
                if isinstance(x.children[0], Expr) and x.children[0].kind == "name":
                    if x.children[0].value == "make" and raw_args and isinstance(raw_args[0], Expr) and raw_args[0].kind == "chan":
                        cap = self.expr(raw_args[1]) if len(raw_args) > 1 else "0"
                        return f"_go_runtime.Channel(capacity={cap})"
                    if x.children[0].value == "new" and raw_args:
                        return f"{self.expr(raw_args[0])}()"
                args = ", ".join(self.expr(a) for a in raw_args)
                return f"{fn}({args})"
            if k == "index": return f"_go_index({self.expr(x.children[0])}, {self.expr(x.children[1])})"
            if k == "selector": return f"{self.expr(x.children[0])}.{py_ident(x.value)}"
            if k == "composite":
                base = x.value
                if isinstance(base, StructType):
                    fields = []
                    positional = []
                    for a in x.children:
                        if isinstance(a, Expr) and a.kind == "keyed":
                            key = repr(a.children[0].value) if isinstance(a.children[0], Expr) and a.children[0].kind == "name" else self.expr(a.children[0])
                            fields.append(f"**{{{key}: {self.expr(a.children[1])}}}")
                        else:
                            positional.append(self.expr(a))
                    if fields:
                        return "_go_struct(" + ", ".join(fields) + ")"
                    if not positional:
                        defaults = []
                        for f in base.fields:
                            for n in f.names:
                                if n != "_":
                                    defaults.append(f"{py_ident(n)}=None")
                        return "_go_struct(" + ", ".join(defaults) + ")"
                    if positional:
                        return "_go_struct(" + ", ".join(f"_{i}={v}" for i, v in enumerate(positional)) + ")"
                    return "_go_struct()"
                if isinstance(base, Expr) and base.kind in ("type_name", "name", "selector"):
                    # Struct literals become Python object construction.  Go
                    # permits omitted fields, so generated constructors give
                    # fields Python None defaults.
                    if any(isinstance(a, Expr) and a.kind == "keyed" for a in x.children):
                        # Named struct literals use identifier field keys;
                        # named map literals may use arbitrary expressions such
                        # as integer constants.  The latter cannot be expressed
                        # as Python keyword arguments, so construct the mapping
                        # explicitly and pass it to the named dict subclass.
                        keyed = [a for a in x.children if isinstance(a, Expr) and a.kind == "keyed"]
                        if any(not (isinstance(a.children[0], Expr) and a.children[0].kind == "name") for a in keyed):
                            pairs=[]
                            for a in x.children:
                                if isinstance(a, Expr) and a.kind == "keyed":
                                    pairs.append(f"{self.expr(a.children[0])}: {self.expr(a.children[1])}")
                                else:
                                    pairs.append(f"{len(pairs)}: {self.expr(a)}")
                            return f"{self.expr(base)}({{{', '.join(pairs)}}})"
                        kwargs=[]
                        positional=[]
                        for a in x.children:
                            if isinstance(a, Expr) and a.kind == "keyed":
                                key = repr(a.children[0].value)
                                kwargs.append(f"**{{{key}: {self.expr(a.children[1])}}}")
                            else:
                                positional.append(self.expr(a))
                        return f"{self.expr(base)}(" + ", ".join(positional + kwargs) + ")"
                    return f"{self.expr(base)}(" + ", ".join(self.expr(a) for a in x.children) + ")"
                if any(isinstance(a, Expr) and a.kind == "keyed" for a in x.children):
                    pairs=[]
                    for a in x.children:
                        if isinstance(a, Expr) and a.kind == "keyed":
                            pairs.append(f"{self.expr(a.children[0])!r}: {self.expr(a.children[1])}")
                        else:
                            pairs.append(f"{len(pairs)}: {self.expr(a)}")
                    return "{" + ", ".join(pairs) + "}"
                return "[" + ", ".join(self.expr(a) for a in x.children) + "]"
            if k == "array": return self.type_expr(x)
            if k == "chan": return "Channel()"
            if k == "pointer": return self.type_expr(x)
            if k == "map": return "dict"
        if isinstance(x, str): return py_ident(x)
        return repr(x)

    def literal(self, text: str) -> str:
        if re.match(r"^0[xX].*[pP][+-]?[0-9]", text):
            return f"float.fromhex({text.replace('_', '')!r})"
        if text.endswith("i") and re.match(r"^[0-9]", text):
            return text[:-1] + "j"
        if re.match(r"^0[0-7]+$", text) and len(text) > 1:
            return "0o" + text[1:]
        if text.startswith("`"):
            return repr(text[1:-1])
        if text.startswith("'"):
            value = ast.literal_eval(text)
            return str(ord(value))
        # Underscores are legal in numeric literals but are also ordinary
        # characters in quoted Go strings (e.g. the base64 URL alphabet).
        # Never strip them from string literals.
        if text.startswith('"'):
            return text
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



_GO_PACKAGE_CACHE: Dict[str, "GoPackage"] = {}


def _go_panic(value=None):
    raise RuntimeError(value)


def _go_recover():
    return None


def _go_deref(value):
    """Read through a translated Go pointer/reference value."""
    if hasattr(value, "get") and callable(value.get):
        return value.get()
    if isinstance(value, dict) and "value" in value:
        return value["value"]
    return value


def _go_store_deref(pointer, value):
    """Store through a translated Go pointer/reference value."""
    if hasattr(pointer, "set") and callable(pointer.set):
        pointer.set(value)
        return value
    if isinstance(pointer, dict) and "value" in pointer:
        pointer["value"] = value
        return value
    # Keep translation executable even where the pointer backend is not yet
    # materialized; the value is intentionally returned for expression-style
    # lowering and later runtime implementations can provide get/set.
    return value


def _go_len(x):
    return 0 if isinstance(x, type) else len(x)


def _go_cap(x):
    return 0 if isinstance(x, type) else len(x)


def _go_copy(dst, src):
    if isinstance(src, str):
        src = src.encode("latin-1" if all(ord(ch) <= 255 for ch in src) else "utf-8")
    n = min(len(dst), len(src))
    dst[:n] = src[:n]
    return n


def _go_index(base, index):
    """Apply Go indexing semantics where Python's defaults differ."""
    if isinstance(base, str) and isinstance(index, int):
        data = base.encode("utf-8")
        return data[index]
    return base[index]


def _go_set_index(base, index, value):
    base[index] = value
    return value


def _go_copy_slice(base, lo, hi, src):
    if isinstance(src, str):
        src = src.encode("latin-1" if all(ord(ch) <= 255 for ch in src) else "utf-8")
    start = 0 if lo is None else lo
    end = len(base) if hi is None else hi
    n = min(end - start, len(src))
    base[start:start+n] = src[:n]
    return n


def _go_append(seq, *values):
    if seq is None:
        seq = []
    seq = list(seq)
    seq.extend(values)
    return seq


def _go_make(type_or_zero=None, size=0, *extra):
    if isinstance(size, int):
        return [None] * size
    return []


_GO_PREDECLARED = {
    "bool": bool, "byte": int, "rune": int, "string": str,
    "int": int, "int8": int, "int16": int, "int32": int, "int64": int,
    "uint": int, "uint8": int, "uint16": int, "uint32": int, "uint64": int,
    "uintptr": int, "float32": float, "float64": float,
    "complex64": complex, "complex128": complex,
    "any": object, "error": Exception,
    "panic": _go_panic, "recover": _go_recover, "append": _go_append,
    "make": _go_make, "len": _go_len, "cap": _go_cap, "copy": _go_copy,
}


class GoPackage(dict):
    """Dictionary-backed Go package namespace with Go-style selector access."""
    def __getattr__(self, name: str) -> Any:
        try:
            return self[name]
        except KeyError as exc:
            raise AttributeError(name) from exc

    def __setattr__(self, name: str, value: Any) -> None:
        self[name] = value


def _go_disk_candidates(import_path: str, search_paths: Optional[Sequence[str]] = None) -> List[Path]:
    candidates: List[Path] = []
    raw = Path(import_path)
    if raw.is_absolute():
        candidates.append(raw)
    roots = list(search_paths or ())
    for env_name in ("GO_PATH", "GOPATH", "GOROOT"):
        value = os.environ.get(env_name)
        if value:
            roots.extend(value.split(os.pathsep))
    roots.append(os.getcwd())
    seen: Set[str] = set()
    for root in roots:
        for candidate in (Path(root) / import_path, Path(root) / "src" / import_path):
            key = os.path.normcase(os.path.abspath(str(candidate)))
            if key not in seen:
                seen.add(key)
                candidates.append(candidate)
    return candidates


def _load_python_file(path: Path, module_name: str) -> Dict[str, Any]:
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load Python package file: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return GoPackage(vars(module))


_GO_BUILD_ENV = None
_GO_BUILD_CACHE = {}


def _go_build_env():
    global _GO_BUILD_ENV
    if _GO_BUILD_ENV is None:
        try:
            out = subprocess.check_output(["go", "env", "GOOS", "GOARCH", "CGO_ENABLED", "GOVERSION"], text=True)
            goos, goarch, cgo, goversion = out.splitlines()[:4]
        except Exception:
            import sys
            goos = {"linux": "linux", "darwin": "darwin", "win32": "windows"}.get(sys.platform, sys.platform)
            goarch = "amd64"
            cgo = "1"
            goversion = "go1.23"
        tags = {goos, goarch, "cgo" if cgo == "1" else ""}
        tags |= {"unix"} if goos in {"aix", "android", "darwin", "dragonfly", "freebsd", "hurd", "illumos", "ios", "linux", "netbsd", "openbsd", "solaris"} else set()
        m = re.match(r"go1\.(\d+)", goversion)
        current_go_minor = int(m.group(1)) if m else 0
        tags |= {f"go1.{i}" for i in range(1, current_go_minor + 1)}
        _GO_BUILD_ENV = (goos, goarch, tags)
    return _GO_BUILD_ENV


def _build_expr_ok(expr: str) -> bool:
    """Evaluate the common Go build-constraint boolean grammar."""
    _, _, tags = _go_build_env()
    toks = re.findall(r"!|&&|\|\||\(|\)|[A-Za-z0-9_./-]+", expr)
    pos = 0
    def atom():
        nonlocal pos
        if pos < len(toks) and toks[pos] == "!":
            pos += 1; return not atom()
        if pos < len(toks) and toks[pos] == "(":
            pos += 1; v = or_expr();
            if pos < len(toks) and toks[pos] == ")": pos += 1
            return v
        if pos >= len(toks): return False
        v = toks[pos] in tags; pos += 1; return v
    def and_expr():
        nonlocal pos
        v = atom()
        while pos < len(toks) and toks[pos] == "&&": pos += 1; v = v and atom()
        return v
    def or_expr():
        nonlocal pos
        v = and_expr()
        while pos < len(toks) and toks[pos] == "||": pos += 1; v = v or and_expr()
        return v
    return or_expr() if toks else True


def _go_source_allowed(path: Path) -> bool:
    key = str(path)
    if key in _GO_BUILD_CACHE:
        return _GO_BUILD_CACHE[key]
    name = path.name
    if name.endswith("_test.go"):
        ok = False
    else:
        goos, goarch, _ = _go_build_env()
        stem = name[:-3]
        # Go's filename constraints: *_GOOS.go, *_GOARCH.go, *_GOOS_GOARCH.go.
        parts = stem.split("_")
        if len(parts) >= 2 and parts[-1] in {
            "amd64", "arm64", "386", "arm", "loong64", "ppc64", "ppc64le",
            "riscv64", "s390x", "mips", "mipsle", "mips64", "mips64le",
            "mips64p32", "mips64p32le", "wasm",
        }:
            ok = parts[-1] == goarch
            if len(parts) >= 3 and parts[-2] in {"aix", "android", "darwin", "dragonfly", "freebsd", "hurd", "illumos", "ios", "js", "linux", "netbsd", "openbsd", "plan9", "solaris", "wasip1", "windows"}:
                ok = ok and parts[-2] == goos
        elif len(parts) >= 2 and parts[-1] in {"aix", "android", "darwin", "dragonfly", "freebsd", "hurd", "illumos", "ios", "js", "linux", "netbsd", "openbsd", "plan9", "solaris", "wasip1", "windows"}:
            ok = parts[-1] == goos
        else:
            ok = True
        if ok:
            try:
                text = path.read_text(encoding="utf-8")
                m = re.search(r"(?m)^\s*//go:build\s+(.+?)\s*$", text)
                if m:
                    ok = _build_expr_ok(m.group(1))
                else:
                    plus = re.findall(r"(?m)^\s*//\s*\+build\s+(.+?)\s*$", text)
                    if plus:
                        ok = any(all(tag in _go_build_env()[2] for tag in line.split()) for line in plus)
            except Exception:
                ok = True
    _GO_BUILD_CACHE[key] = ok
    return ok


def _go_disk_package_name(import_path: str, search_paths: Optional[Sequence[str]]) -> Optional[str]:
    """Read the declared Go package name for an import path when available."""
    for candidate in _go_disk_candidates(import_path, search_paths):
        if not candidate.is_dir():
            continue
        for go_file in sorted(candidate.glob("*.go")):
            if not _go_source_allowed(go_file):
                continue
            try:
                text = go_file.read_text(encoding="utf-8")
            except OSError:
                continue
            match = re.search(r"(?m)^\s*package\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:;|$)", text)
            if match:
                return match.group(1)
    return None


def load_go_package(
    import_path: str,
    imports: Optional[Dict[str, Any]] = None,
    *,
    search_paths: Optional[Sequence[str]] = None,
    execute: bool = True,
) -> Dict[str, Any]:
    """Load a Go package from disk; translate its .go files into one namespace.

    Filesystem resolution is intentional: Go import paths are not treated as
    Python module names. A package directory may provide a Python shim or Go
    source files.
    """
    cache = imports if imports is not None else {}
    # Package imports form cycles in the real standard library (for example
    # fmt -> errors -> internal/... -> fmt).  Keep one process-wide package
    # cache so nested package loaders see the same partially initialized
    # namespace instead of recursively translating the package forever.
    if import_path in _GO_PACKAGE_CACHE:
        pkg = _GO_PACKAGE_CACHE[import_path]
        cache[import_path] = pkg
        return pkg
    if import_path in cache:
        return cache[import_path]

    # fmt only needs a small reflective boundary for primitive formatting.
    # Keep that boundary host-backed rather than recursively translating the
    # entire reflect/runtime implementation.  The fmt implementation itself
    # remains the real Go source from GOROOT.
    if import_path == "reflect":
        import copy as _copy

        _kind_names = {
            "Invalid": 0, "Bool": 1, "Int": 2, "Int8": 3, "Int16": 4,
            "Int32": 5, "Int64": 6, "Uint": 7, "Uint8": 8, "Uint16": 9,
            "Uint32": 10, "Uint64": 11, "Uintptr": 12, "Float32": 14,
            "Float64": 15, "Complex64": 16, "Complex128": 17, "Array": 17 + 1,
            "Chan": 18 + 1, "Func": 19 + 1, "Interface": 20 + 1,
            "Map": 21 + 1, "Pointer": 22 + 1, "Slice": 23 + 1,
            "String": 24 + 1, "Struct": 25 + 1, "UnsafePointer": 26 + 1,
        }

        class _Type:
            def __init__(self, value=None): self.value = value
            def String(self): return type(self.value).__name__ if self.value is not None else "<nil>"
            def Kind(self): return _kind(self.value)

        def _kind(value):
            if value is None: return _kind_names["Invalid"]
            if isinstance(value, bool): return _kind_names["Bool"]
            if isinstance(value, int): return _kind_names["Int"]
            if isinstance(value, float): return _kind_names["Float64"]
            if isinstance(value, complex): return _kind_names["Complex128"]
            if isinstance(value, str): return _kind_names["String"]
            if isinstance(value, (bytes, bytearray)): return _kind_names["Slice"]
            if isinstance(value, dict): return _kind_names["Map"]
            if isinstance(value, (list, tuple)): return _kind_names["Slice"]
            if callable(value): return _kind_names["Func"]
            return _kind_names["Struct"]

        class _Value:
            def __init__(self, value=None): self._value = value
            def Kind(self): return _kind(self._value)
            def UnsafePointer(self): return id(self._value) if self._value is not None else 0
            def Type(self): return _Type(self._value)
            def IsValid(self): return self._value is not None
            def CanInterface(self): return True
            def Interface(self): return self._value
            def IsNil(self): return self._value is None
            def String(self): return str(self._value)

        def _ValueOf(value): return _Value(value)
        def _TypeOf(value): return _Type(value)
        def _DeepEqual(a, b): return a == b
        def _MakeSlice(typ, length, cap): return [None] * int(length)

        ns = GoPackage({"__name__": "reflect", "Value": _Value, "Type": _Type,
                        "ValueOf": _ValueOf, "TypeOf": _TypeOf,
                        "DeepEqual": _DeepEqual, "MakeSlice": _MakeSlice})
        ns.update(_kind_names)
        _GO_PACKAGE_CACHE[import_path] = ns
        cache[import_path] = ns
        return ns

    # fmt uses sync.Pool for printer/scanner reuse.  Keep that synchronization
    # boundary host-backed; fmt itself and its formatting implementation remain
    # the real Go sources loaded from disk.
    if import_path == "sync":
        import threading as _threading

        class _Pool:
            def __init__(self, New=None):
                self.New = New
                self._items = []

            def Get(self):
                if self._items:
                    return self._items.pop()
                return self.New() if self.New is not None else None

            def Put(self, x):
                if x is not None:
                    self._items.append(x)

        class _Map:
            def __init__(self):
                self._data = {}
                self._lock = _threading.RLock()

            def Load(self, key):
                with self._lock:
                    if key in self._data:
                        return self._data[key], True
                    return None, False

            def Store(self, key, value):
                with self._lock:
                    self._data[key] = value

            def LoadOrStore(self, key, value):
                with self._lock:
                    if key in self._data:
                        return self._data[key], True
                    self._data[key] = value
                    return value, False

            def Delete(self, key):
                with self._lock:
                    self._data.pop(key, None)

            def Range(self, fn):
                with self._lock:
                    items = list(self._data.items())
                for key, value in items:
                    if not fn(key, value):
                        break

        class _Mutex:
            def __init__(self): self._lock = _threading.RLock()
            def Lock(self): self._lock.acquire()
            def Unlock(self): self._lock.release()
            def TryLock(self): return self._lock.acquire(blocking=False)

        class _Once:
            def __init__(self): self._once = _threading.Lock(); self._done = False
            def Do(self, fn):
                if not self._done:
                    with self._once:
                        if not self._done:
                            fn(); self._done = True

        class _WaitGroup:
            def __init__(self): self._cv = _threading.Condition(); self._n = 0
            def Add(self, n):
                with self._cv:
                    self._n += n
                    if self._n <= 0: self._cv.notify_all()
            def Done(self): self.Add(-1)
            def Wait(self):
                with self._cv:
                    while self._n > 0: self._cv.wait()

        ns = GoPackage({"__name__": "sync", "Pool": _Pool, "Map": _Map,
                        "Mutex": _Mutex, "RWMutex": _Mutex, "Once": _Once,
                        "WaitGroup": _WaitGroup})
        _GO_PACKAGE_CACHE[import_path] = ns
        cache[import_path] = ns
        return ns

    # Go 1.24+ also provides crypto/sha3. Older host toolchains can still
    # load vendored x/crypto/sha3 through Python's hashlib implementation.
    if import_path == "crypto/sha3":
        import hashlib as _hashlib
        def _new(name): return lambda: _hashlib.new(name)
        def _sum(name, data): return _hashlib.new(name, bytes(data)).digest()
        class _Shake:
            def __init__(self, name): self._h = getattr(_hashlib, name)()
            def Write(self, data): self._h.update(bytes(data)); return len(data), None
            def Read(self, n): return self._h.digest(int(n)), None
            def Sum(self, prefix=b""): return bytes(prefix) + self._h.digest()
        ns = GoPackage({"__name__": import_path,
            "New224": _new("sha3_224"), "New256": _new("sha3_256"),
            "New384": _new("sha3_384"), "New512": _new("sha3_512"),
            "Sum224": lambda d: _sum("sha3_224", d), "Sum256": lambda d: _sum("sha3_256", d),
            "Sum384": lambda d: _sum("sha3_384", d), "Sum512": lambda d: _sum("sha3_512", d),
            "NewSHAKE128": lambda: _Shake("shake_128"), "NewSHAKE256": lambda: _Shake("shake_256"),
            "NewCSHAKE128": lambda *a: _Shake("shake_128"), "NewCSHAKE256": lambda *a: _Shake("shake_256"),
            "SHAKE": object})
        _GO_PACKAGE_CACHE[import_path] = ns; cache[import_path] = ns; return ns

    # Go 1.24+ adds crypto/hkdf to the standard library. If the host Go
    # toolchain predates it, provide the small API boundary needed by vendored
    # dependencies rather than selecting an incompatible source tree.
    if import_path == "crypto/hkdf":
        import hashlib as _hashlib
        import hmac as _hmac

        def _hash_factory(hashfn):
            if callable(hashfn):
                try:
                    h = hashfn()
                    if hasattr(h, "digest") and hasattr(h, "copy"):
                        return h
                except Exception:
                    pass
            return _hashlib.sha256()

        def _digestmod(hashfn):
            return _hash_factory(hashfn).__class__

        def _extract(hashfn, secret, salt):
            if not salt:
                salt = b"\x00" * _hash_factory(hashfn).digest_size
            return _hmac.new(bytes(salt), bytes(secret), _digestmod(hashfn)).digest()

        class _Reader:
            def __init__(self, hashfn, prk, info):
                self.hashfn = hashfn
                self.prk = bytes(prk)
                self.info = bytes(info or b"")
                self.counter = 1
                self.prev = b""
                self.buf = b""

            def Read(self, p):
                need = len(p)
                out = bytearray(self.buf)
                self.buf = b""
                while len(out) < need and self.counter <= 255:
                    out.extend(_hmac.new(
                        self.prk, self.prev + self.info + bytes([self.counter]),
                        _digestmod(self.hashfn)).digest())
                    self.prev = bytes(out[-_hash_factory(self.hashfn).digest_size:])
                    self.counter += 1
                if len(out) < need:
                    return 0, Exception("hkdf: entropy limit reached")
                data = bytes(out[:need])
                self.buf = bytes(out[need:])
                p[:need] = data
                return need, None

        def _expand(hashfn, prk, info):
            return _Reader(hashfn, prk, info)

        ns = GoPackage({"__name__": import_path, "Extract": _extract,
                        "Expand": _expand,
                        "New": lambda h, secret, salt, info: _expand(h, _extract(h, secret, salt), info)})
        _GO_PACKAGE_CACHE[import_path] = ns
        cache[import_path] = ns
        return ns

    # The real fmt package writes through os.Stdout/Stderr.  The os package
    # itself is heavily platform/runtime dependent, so keep only its file
    # writer boundary host-backed while still translating fmt itself from the
    # actual Go source tree.
    if import_path == "os":
        import sys as _sys

        class _File:
            def __init__(self, stream):
                self._stream = stream

            def Write(self, data):
                if isinstance(data, (bytes, bytearray)):
                    text = bytes(data).decode("utf-8", "replace")
                elif isinstance(data, (list, tuple)):
                    parts = []
                    for item in data:
                        if isinstance(item, int):
                            parts.append(chr(item & 0xff))
                        else:
                            parts.append(str(item))
                    text = "".join(parts)
                else:
                    text = str(data)
                self._stream.write(text)
                self._stream.flush()
                return len(data), None

            def WriteString(self, text):
                self._stream.write(str(text))
                self._stream.flush()
                return len(str(text)), None

        ns = GoPackage({
            "__name__": "os",
            "File": _File,
            "Stdout": _File(_sys.stdout),
            "Stderr": _File(_sys.stderr),
            "Stdin": _File(_sys.stdin),
        })
        _GO_PACKAGE_CACHE[import_path] = ns
        cache[import_path] = ns
        return ns

    # cgo's `C` pseudo-package has no filesystem representation.  The Go
    # parser/lowerer needs a namespace for cgo-generated declarations so that
    # pure-Python loading can continue; actual native calls remain an
    # environment boundary and are deliberately represented by inert shims.
    if import_path == "C":
        class _CShim(GoPackage):
            def __getattr__(self, name):
                if name in self:
                    return self[name]
                if name in {"char", "uchar", "short", "ushort", "int", "uint", "long", "ulong", "longlong", "ulonglong", "size_t", "ssize_t", "uid_t", "gid_t", "socklen_t"}:
                    value = int
                elif name.startswith("struct_"):
                    value = type(name, (), {})
                elif name in {"GoString"}:
                    value = lambda x=None: str(x)
                elif (name.startswith(("AF_", "IPPROTO_", "SOCK_", "EAI_", "_SC_"))
                      or name.isupper()):
                    value = 0
                else:
                    value = lambda *args, **kwargs: 0
                self[name] = value
                return value
        ns = _CShim({"__name__": "C"})
        _GO_PACKAGE_CACHE[import_path] = ns
        cache[import_path] = ns
        return ns

    # The Go "unsafe" pseudo-package cannot be expressed as .go source and
    # has no disk representation.  Provide a Python shim so that packages
    # that import it (e.g. runtime, reflect) remain executable.
    if import_path == "unsafe":
        _ptr_size = 8 if _go_build_env()[1] in {
            "amd64", "arm64", "loong64", "mips64", "mips64le",
            "ppc64", "ppc64le", "riscv64", "s390x"} else 4

        def _Sizeof(x=None):  # type: ignore[override]
            # Keep compile-time size expressions executable without pretending
            # that every Go value is a slice.  Translated structs/scalars use
            # one machine word as a conservative approximation; sequence-like
            # values retain the three-word slice-header approximation.
            if isinstance(x, (list, tuple, bytes, bytearray)):
                return _ptr_size * 3
            return _ptr_size

        def _Alignof(x=None):
            return _ptr_size

        def _Offsetof(x=None):
            return 0

        def _Pointer(x=None):
            return x

        def _Add(ptr=None, length=0):
            return ptr

        def _Slice(ptr=None, length=0):
            return []

        def _SliceData(s=None):
            return None

        def _String(ptr=None, length=0):
            return ""

        def _StringData(s=None):
            return None

        ns = GoPackage({
            "__name__": "unsafe",
            "Sizeof": _Sizeof,
            "Alignof": _Alignof,
            "Offsetof": _Offsetof,
            "Pointer": _Pointer,
            "Add": _Add,
            "Slice": _Slice,
            "SliceData": _SliceData,
            "String": _String,
            "StringData": _StringData,
        })
        _GO_PACKAGE_CACHE["unsafe"] = ns
        cache["unsafe"] = ns
        return ns

    candidates = _go_disk_candidates(import_path, search_paths)
    for candidate in candidates:
        if candidate.is_file() and candidate.suffix == ".py":
            ns = _load_python_file(candidate, f"go_disk_{py_ident(import_path)}")
            _GO_PACKAGE_CACHE[import_path] = ns
            cache[import_path] = ns
            return ns
        if candidate.is_dir():
            for py_file in (candidate / "__init__.py", candidate / f"{candidate.name}.py"):
                if py_file.exists():
                    ns = _load_python_file(py_file, f"go_disk_{py_ident(import_path)}")
                    _GO_PACKAGE_CACHE[import_path] = ns
                    cache[import_path] = ns
                    return ns
            go_files = sorted(p for p in candidate.glob("*.go") if _go_source_allowed(p))
            if go_files:
                # Files such as goarch_arm64.go define constants referenced by
                # goarch.go.  Go itself resolves package declarations independent
                # of filename order; our Python executor does not, so put the
                # architecture-specific implementation file ahead of goarch.go.
                go_files.sort(key=lambda p: (
                    2 if p.name == "goarch.go" else 0,
                    p.name,
                ))
                ns: GoPackage = GoPackage({"__name__": import_path, "__go_imports__": {}})
                ns.update(_GO_PREDECLARED)
                # Go source files in a package are not semantically ordered by
                # filename.  The generated architecture files contain constants
                # consumed by goarch.go, so load architecture-specific files
                # first when translating the real standard library.
                ns["__go_runtime_ptr_size__"] = (
                    8 if _go_build_env()[1] in {"amd64", "arm64", "loong64", "mips64",
                                                "mips64le", "ppc64", "ppc64le",
                                                "riscv64", "s390x"} else 4
                )
                # Publish before executing files: Go's package graph may be
                # cyclic, and dependants must be able to reference this
                # partially constructed namespace.
                _GO_PACKAGE_CACHE[import_path] = ns
                cache[import_path] = ns
                generated_files = []
                for go_file in go_files:
                    generated = translate_go(
                        go_file.read_text(encoding="utf-8"),
                        module_name=py_ident(candidate.name),
                        import_paths=search_paths,
                    )
                    generated_files.append((go_file, generated))

                # Go declarations are package-scoped and their source-file
                # order is not semantically significant.  Python exec is
                # sequential, however, so package constants such as
                # internal/goarch's AMD64/_ArchFamily/IsArm64 dependencies can
                # temporarily refer to declarations from another file.  Retry
                # files which fail specifically because a package name has not
                # been initialized yet.  This is deliberately limited to
                # NameError: real runtime errors must still surface immediately.
                if not execute:
                    from go_parser import parse_go
                    ns["__go_generated_files__"] = {str(go_file): generated for go_file, generated in generated_files}
                    ns["__go_files__"] = [str(go_file) for go_file, _ in generated_files]
                    child_imports = set()
                    for go_file in go_files:
                        tree = parse_go(go_file.read_text(encoding="utf-8"))
                        child_imports.update(imp.path for imp in tree.imports)
                    for child in sorted(child_imports):
                        if child not in {"C", "unsafe"}:
                            load_go_package(child, cache, search_paths=search_paths, execute=False)
                    return ns

                pending = list(generated_files)
                last_error = None
                while pending:
                    next_pending = []
                    progress = False
                    for go_file, generated in pending:
                        try:
                            exec(compile(generated, str(go_file), "exec"), ns, ns)
                            progress = True
                        except (NameError, KeyError, AttributeError, TypeError) as exc:
                            # These can be cross-file initialization-order
                            # misses: Go packages share one namespace even
                            # though their source files are compiled as a
                            # single unit.  A translated method can also be
                            # referenced by a package-level initializer before
                            # the source file containing that method has been
                            # executed.  In that case Python reports a missing
                            # receiver/argument on the generated method.
                            # Retry only that distinctive TypeError shape;
                            # genuine TypeErrors still surface immediately once
                            # no package file can make progress.
                            retryable_type_error = (
                                isinstance(exc, TypeError)
                                and "missing" in str(exc)
                                and "required positional argument" in str(exc)
                            )
                            if isinstance(exc, TypeError) and not retryable_type_error:
                                raise
                            last_error = exc
                            next_pending.append((go_file, generated))
                    if not next_pending:
                        break
                    if not progress:
                        go_file, _ = next_pending[0]
                        raise last_error.with_traceback(last_error.__traceback__)
                    pending = next_pending
                return ns

    tried = "\n  ".join(str(p) for p in candidates)
    raise ImportError(
        f"Go package {import_path!r} was not found on disk. Tried:\n  {tried}\n"
        "Pass import_paths=[...] or set GOPATH/GO_PATH/GOROOT."
    )


def lower_go(
    tree: File,
    module_name: str = "translated_go",
    runtime_bindings: Optional[Mapping[str, str]] = None,
    import_paths: Optional[Sequence[str]] = None,
) -> str:
    return Lowerer(
        module_name,
        runtime_bindings=runtime_bindings,
        import_paths=import_paths,
    ).lower(tree)


def translate_go(
    source: str,
    module_name: str = "translated_go",
    runtime_bindings: Optional[Mapping[str, str]] = None,
    import_paths: Optional[Sequence[str]] = None,
) -> str:
    from go_parser import parse_go
    return lower_go(
        parse_go(source),
        module_name,
        runtime_bindings=runtime_bindings,
        import_paths=import_paths,
    )
