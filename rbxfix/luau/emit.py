"""Luau source printer."""
import math
import struct

from .ast import (Assign, BinOp, Break, Call, CallStmt, Closure, Comment, Concat, Const, IfExpr,
                  Continue, Do, GenFor, Global, If, Index, LocalDecl, MethodCall, Name, NumFor,
                  Raw, RegDef, RegRef, Repeat, Return, TableCons, UnOp, Upval, Vararg, While,
                  deref)
from .cfg import DecompileError, SetList
from .scope import is_field_name, is_identifier

PREC = {"or": 1, "and": 2, "<": 3, ">": 3, "<=": 3, ">=": 3, "~=": 3, "==": 3, "..": 4,
        "+": 5, "-": 5, "*": 6, "/": 6, "//": 6, "%": 6, "^": 8}
UNARY = 7
ATOM = 10
RIGHT_ASSOC = {"..", "^"}


def fmt_number(v):
    if v != v:
        return "0 / 0", 6
    if v == math.inf:
        return "math.huge", ATOM
    if v == -math.inf:
        return "-math.huge", UNARY
    if v == int(v) and abs(v) < 2 ** 53:
        if v == 0 and math.copysign(1, v) < 0:
            return "-0", UNARY
        s = str(int(v))
    else:
        s = repr(v)
    if s.startswith("-"):
        return s, UNARY
    return s, ATOM


def fmt_float32(v):
    if v != v:
        return "0 / 0"
    if math.isinf(v):
        return "math.huge" if v > 0 else "-math.huge"
    if v == int(v) and abs(v) < 2 ** 24:
        return str(int(v))
    packed = struct.pack("<f", v)
    for prec in range(1, 18):
        s = "%.*g" % (prec, v)
        if struct.pack("<f", float(s)) == packed:
            return s
    return repr(v)


_ESC = {7: "\\a", 8: "\\b", 9: "\\t", 10: "\\n", 11: "\\v", 12: "\\f", 13: "\\r",
        34: '\\"', 92: "\\\\"}


def fmt_string(b):
    if isinstance(b, str):
        b = b.encode("utf-8")
    out = ['"']
    i = 0
    n = len(b)
    while i < n:
        c = b[i]
        if c in _ESC:
            out.append(_ESC[c])
            i += 1
        elif 32 <= c < 127:
            out.append(chr(c))
            i += 1
        elif c >= 0x80:
            # keep valid UTF-8 sequences readable
            ln = 2 if 0xC2 <= c <= 0xDF else 3 if 0xE0 <= c <= 0xEF else 4 if 0xF0 <= c <= 0xF4 else 0
            seq = b[i:i + ln]
            ok = False
            if ln and len(seq) == ln:
                try:
                    seq.decode("utf-8")
                    ok = True
                except UnicodeDecodeError:
                    ok = False
            if ok:
                out.append(seq.decode("utf-8"))
                i += ln
            else:
                out.append("\\%03d" % c)
                i += 1
        else:
            out.append("\\%03d" % c)
            i += 1
    out.append('"')
    return "".join(out)


def _interp_parts(e):
    """If `e` is ("...%*..."):format(a, b) as produced by Luau string
    interpolation, return the literal pieces; else None."""
    if type(e) is not MethodCall or e.name != b"format":
        return None
    o = deref(e.obj)
    if type(o) is not Const or o.kind != "string":
        return None
    fmt = o.value
    pieces = []
    cur = bytearray()
    i = 0
    n = len(fmt)
    nargs = 0
    while i < n:
        c = fmt[i]
        if c == 37:  # '%'
            if i + 1 < n and fmt[i + 1] == 42:      # %*
                pieces.append(bytes(cur))
                cur = bytearray()
                nargs += 1
                i += 2
                continue
            if i + 1 < n and fmt[i + 1] == 37:      # %%
                cur.append(37)
                i += 2
                continue
            return None
        cur.append(c)
        i += 1
    pieces.append(bytes(cur))
    if nargs != len(e.args) or nargs == 0:
        return None
    for a in e.args:
        if _is_multi(a) and deref(a).nret == -1:
            return None
    return pieces


def _fmt_interp_piece(b):
    s = fmt_string(b)[1:-1]
    return s.replace("`", "\\`").replace("{", "\\{").replace("}", "\\}")


# imported builtins that always return exactly one value: no need for (f(x))
_SINGLE_RESULT = {
    ("tostring",), ("tonumber",), ("type",), ("typeof",), ("rawget",), ("rawequal",),
    ("rawlen",), ("setmetatable",), ("getmetatable",),
    ("string", "format"), ("string", "sub"), ("string", "len"), ("string", "lower"),
    ("string", "upper"), ("string", "rep"), ("string", "reverse"), ("table", "concat"),
    ("table", "create"), ("table", "clone"), ("table", "freeze"),
    ("math", "floor"), ("math", "ceil"), ("math", "abs"), ("math", "max"), ("math", "min"),
    ("math", "clamp"), ("math", "round"), ("math", "sqrt"), ("math", "sign"),
}


def _import_path(e):
    parts = []
    e = deref(e)
    while type(e) is Index:
        k = deref(e.key)
        if type(k) is not Const or k.kind != "string":
            return None
        parts.append(k.value.decode("utf-8", "replace"))
        e = deref(e.obj)
    if type(e) is not Global or not e.imported:
        return None
    parts.append(e.name)
    return tuple(reversed(parts))


def _is_multi(e):
    e = deref(e)
    t = type(e)
    if t is MethodCall and _interp_parts(e) is not None:
        return False
    if t is Call and _import_path(e.func) in _SINGLE_RESULT:
        return False
    return t is Call or t is MethodCall or t is Vararg


class Emitter:
    def __init__(self, decompiler):
        self.dc = decompiler
        self.lines = []
        self.indent = 0

    def line(self, s):
        self.lines.append("\t" * self.indent + s)

    # ----------------------------------------------------------- exprs
    def name_of(self, web):
        if web.name is None:
            raise DecompileError("unnamed variable")
        return web.name

    def expr_list(self, exprs, adjust_last=True):
        parts = []
        n = len(exprs)
        for i, e in enumerate(exprs):
            s = self.expr(e)
            if adjust_last and i == n - 1 and _is_multi(e) and deref(e).nret != -1:
                s = "(" + s + ")"
            parts.append(s)
        return ", ".join(parts)

    def prefix(self, e):
        d = deref(e)
        t = type(d)
        s, p = self.expr_p(d)
        if t is MethodCall and _interp_parts(d) is not None:
            return "(" + s + ")"
        if t in (Global, Index, Call, MethodCall, Upval, Name) or (t is RegRef and d.repl is None):
            return s
        return "(" + s + ")"

    def expr(self, e):
        return self.expr_p(e)[0]

    def expr_p(self, e):
        e = deref(e)
        t = type(e)
        if t is RegRef:
            return self.name_of(e.web), ATOM
        if t is Const:
            k = e.kind
            if k == "nil":
                return "nil", ATOM
            if k == "bool":
                return ("true" if e.value else "false"), ATOM
            if k == "number":
                return fmt_number(e.value)
            if k == "string":
                return fmt_string(e.value), ATOM
            if k == "vector":
                x, y, z = e.value[:3]
                return "Vector3.new(%s, %s, %s)" % (fmt_float32(x), fmt_float32(y), fmt_float32(z)), ATOM
            if k == "integer":
                v = e.value
                return ("%di" % v) if v >= 0 else ("-%di" % -v), (ATOM if v >= 0 else UNARY)
            raise DecompileError("bad constant")
        if t is Global:
            if is_identifier(e.name):
                return e.name, ATOM
            return "getfenv()[%s]" % fmt_string(e.name), ATOM
        if t is Name:
            return e.name, ATOM
        if t is Upval:
            return e.fn.upval_names[e.index], ATOM
        if t is Index:
            obj = self.prefix(e.obj)
            k = deref(e.key)
            if type(k) is Const and k.kind == "string":
                try:
                    ks = k.value.decode("utf-8")
                except UnicodeDecodeError:
                    ks = None
                if ks is not None and is_field_name(ks):
                    return obj + "." + ks, ATOM
            return obj + "[" + self.expr(e.key) + "]", ATOM
        if t is Call:
            return self.prefix(e.func) + "(" + self.expr_list(e.args) + ")", ATOM
        if t is MethodCall:
            pieces = _interp_parts(e)
            if pieces is not None:
                out = ["`"]
                for i, piece in enumerate(pieces):
                    out.append(_fmt_interp_piece(piece))
                    if i < len(e.args):
                        out.append("{" + self.expr(e.args[i]) + "}")
                out.append("`")
                text = "".join(out)
                if "\n" not in text:
                    return text, ATOM
                # multi-line interpolation: keep the explicit format call
                return (self.prefix(e.obj) + ":format(" + self.expr_list(e.args) + ")"), ATOM
            name = e.name.decode("utf-8", "replace")
            if not is_field_name(name):
                raise DecompileError("method name is not an identifier")
            return self.prefix(e.obj) + ":" + name + "(" + self.expr_list(e.args) + ")", ATOM
        if t is Vararg:
            return "...", ATOM
        if t is BinOp:
            p = PREC[e.op]
            a, pa = self.expr_p(e.a)
            b, pb = self.expr_p(e.b)
            if e.op in RIGHT_ASSOC:
                if pa <= p:
                    a = "(" + a + ")"
                if e.op == "^":
                    if pb < UNARY:
                        b = "(" + b + ")"
                elif pb < p:
                    b = "(" + b + ")"
            else:
                if pa < p:
                    a = "(" + a + ")"
                rb = deref(e.b)
                assoc = e.op in ("and", "or") and type(rb) is BinOp and rb.op == e.op
                if pb < p or (pb == p and not assoc):
                    b = "(" + b + ")"
            return a + " " + e.op + " " + b, p
        if t is UnOp:
            a, pa = self.expr_p(e.a)
            if pa < UNARY:
                a = "(" + a + ")"
            if e.op == "not":
                return "not " + a, UNARY
            if e.op == "-" and a.startswith("-"):
                return "- " + a, UNARY
            return e.op + a, UNARY
        if t is Concat:
            parts = []
            for x in e.parts:
                s, p = self.expr_p(x)
                if p <= PREC[".."]:
                    s = "(" + s + ")"
                parts.append(s)
            return " .. ".join(parts), PREC[".."]
        if t is TableCons:
            return self.table(e), ATOM
        if t is Closure:
            return self.closure(e), ATOM
        if t is IfExpr:
            c, pc_ = self.expr_p(e.cond)
            a, pa = self.expr_p(e.a)
            b = self.expr(e.b)
            if pc_ == 0:
                c = "(" + c + ")"
            if pa == 0:
                a = "(" + a + ")"
            return "if %s then %s else %s" % (c, a, b), 0
        raise DecompileError("cannot print %s" % t.__name__)

    def table(self, e):
        if not e.items:
            return "{}"
        self.indent += 1
        try:
            parts = self._table_parts(e)
        finally:
            self.indent -= 1
        flat = "{" + ", ".join(parts) + "}"
        if len(flat) <= 100 and "\n" not in flat:
            return flat
        ind = "\t" * (self.indent + 1)
        return "{\n" + "".join(ind + p + ",\n" for p in parts) + "\t" * self.indent + "}"

    def _table_parts(self, e):
        parts = []
        npos = sum(1 for k, v in e.items if k is None)
        seen_pos = 0
        for k, v in e.items:
            if k is None:
                seen_pos += 1
                s = self.expr(v)
                if seen_pos == npos and _is_multi(v) and deref(v).nret != -1:
                    s = "(" + s + ")"
                parts.append(s)
            else:
                kd = deref(k)
                ks = None
                if type(kd) is Const and kd.kind == "string":
                    try:
                        ks = kd.value.decode("utf-8")
                    except UnicodeDecodeError:
                        ks = None
                if ks is not None and is_identifier(ks):
                    parts.append(ks + " = " + self.expr(v))
                else:
                    parts.append("[" + self.expr(k) + "] = " + self.expr(v))
        # a multi-value positional item must be the last item to keep its values
        if npos:
            lastpos = max(i for i, (k, v) in enumerate(e.items) if k is None)
            lk, lv = e.items[lastpos]
            if _is_multi(lv) and deref(lv).nret == -1 and lastpos != len(e.items) - 1:
                raise DecompileError("multi-value table item not last")
        return parts

    def closure(self, e, name=None):
        child = e.fn
        names = []
        for c in e.captures:
            if type(c) is Upval:
                names.append(c.fn.upval_names[c.index])
            else:
                names.append(self.name_of(c.web))
        return self.dc.emit_function(child, names, self.indent, name)

    # ------------------------------------------------------------ stmts
    def block(self, stmts):
        for s in stmts:
            self.stmt(s)

    def lvalue(self, t):
        tt = type(t)
        if tt is RegDef:
            return self.name_of(t.web)
        if tt is Global:
            return self.expr(t)
        if tt is Upval:
            return t.fn.upval_names[t.index]
        if tt is Index:
            return self.expr(t)
        raise DecompileError("bad assignment target")

    def _func_name_target(self, t):
        """`function a.b.c()` sugar if the target is a plain dotted name."""
        if type(t) is not Index:
            return None
        k = deref(t.key)
        if type(k) is not Const or k.kind != "string":
            return None
        try:
            ks = k.value.decode("utf-8")
        except UnicodeDecodeError:
            return None
        if not is_identifier(ks):
            return None
        o = deref(t.obj)
        if type(o) is Index:
            base = self._func_name_target(o)
        elif type(o) is RegRef or type(o) is Upval or type(o) is Global:
            base = self.expr(o)
            if type(o) is Global and not is_identifier(o.name):
                return None
        else:
            return None
        if base is None:
            return None
        return base + "." + ks

    def emit_stmt_text(self, s):
        if s.startswith("("):
            s = ";" + s
        self.line(s)

    def stmt(self, s):
        t = type(s)
        if t is Assign:
            if len(s.targets) == 1 and len(s.values) == 1 and type(deref(s.values[0])) is Closure:
                clo = deref(s.values[0])
                tg = s.targets[0]
                if s.is_local:
                    nm = self.name_of(tg.web)
                    self.line_multiline("local function " + self.closure(clo, name=nm))
                    return
                fname = None
                if type(tg) is Index:
                    fname = self._func_name_target(tg)
                elif type(tg) is Global and is_identifier(tg.name):
                    fname = tg.name
                elif type(tg) is RegDef:
                    fname = self.name_of(tg.web)
                elif type(tg) is Upval:
                    fname = tg.fn.upval_names[tg.index]
                if fname is not None:
                    self.line_multiline("function " + self.closure(clo, name=fname))
                    return
            lhs = ", ".join(self.lvalue(x) for x in s.targets)
            rhs = ", ".join(self.expr(v) for v in s.values)
            if s.is_local:
                self.line_multiline("local " + lhs + " = " + rhs)
            else:
                self.line_multiline(lhs + " = " + rhs, check_paren=True)
        elif t is CallStmt:
            self.line_multiline(self.expr(s.call), check_paren=True)
        elif t is Return:
            if s.values:
                self.line_multiline("return " + self.expr_list(s.values))
            else:
                self.line("return")
        elif t is LocalDecl:
            self.line("local " + ", ".join(self.name_of(w) for w in s.webs))
        elif t is If:
            self.line_multiline("if " + self.expr(s.cond) + " then")
            self.indent += 1
            self.block(s.then)
            self.indent -= 1
            orelse = s.orelse
            while len(orelse) == 1 and type(orelse[0]) is If:
                ei = orelse[0]
                self.line_multiline("elseif " + self.expr(ei.cond) + " then")
                self.indent += 1
                self.block(ei.then)
                self.indent -= 1
                orelse = ei.orelse
            if orelse:
                self.line("else")
                self.indent += 1
                self.block(orelse)
                self.indent -= 1
            self.line("end")
        elif t is While:
            self.line_multiline("while " + self.expr(s.cond) + " do")
            self.indent += 1
            self.block(s.body)
            self.indent -= 1
            self.line("end")
        elif t is Repeat:
            self.line("repeat")
            self.indent += 1
            self.block(s.body)
            self.indent -= 1
            self.line_multiline("until " + self.expr(s.cond))
        elif t is NumFor:
            step = deref(s.step)
            hdr = "for %s = %s, %s" % (self.name_of(s.var), self.expr(s.start), self.expr(s.limit))
            if not (type(step) is Const and step.kind == "number" and step.value == 1):
                hdr += ", " + self.expr(s.step)
            self.line_multiline(hdr + " do")
            self.indent += 1
            self.block(s.body)
            self.indent -= 1
            self.line("end")
        elif t is GenFor:
            names = ", ".join(self.name_of(v) for v in s.vars)
            if len(s.exprs) == 1:
                ex = self.expr(s.exprs[0])
            else:
                ex = self.expr_list(s.exprs)
            self.line_multiline("for %s in %s do" % (names, ex))
            self.indent += 1
            self.block(s.body)
            self.indent -= 1
            self.line("end")
        elif t is Break:
            self.line("break")
        elif t is Continue:
            self.line("continue")
        elif t is Do:
            self.line("do")
            self.indent += 1
            self.block(s.body)
            self.indent -= 1
            self.line("end")
        elif t is SetList:
            tbl = self.expr(s.table)
            if s.values and s.values[-1].reg == 1000:
                fixed = s.values[:-1]
                for i, v in enumerate(fixed):
                    self.line_multiline("%s[%d] = %s" % (tbl, s.start + i, self.expr(v)), check_paren=True)
                # t[n], t[n+1], ... = <all values of a multi-value expression>
                self.line_multiline(
                    ";(function(t, ...) table.move({...}, 1, select(\"#\", ...), %d, t) end)(%s, %s)"
                    % (s.start + len(fixed), tbl, self.expr(s.values[-1])))
                return
            for i, v in enumerate(s.values):
                self.line_multiline("%s[%d] = %s" % (tbl, s.start + i, self.expr(v)), check_paren=True)
        elif t is Comment:
            for ln in s.text.split("\n"):
                self.line("-- " + ln)
        elif t is Raw:
            for ln in s.text.split("\n"):
                self.line(ln)
        else:
            raise DecompileError("cannot print statement %s" % t.__name__)

    def line_multiline(self, text, check_paren=False):
        if check_paren and text.startswith("("):
            text = ";" + text
        first, *rest = text.split("\n")
        self.lines.append("\t" * self.indent + first)
        for r in rest:
            self.lines.append(r)
