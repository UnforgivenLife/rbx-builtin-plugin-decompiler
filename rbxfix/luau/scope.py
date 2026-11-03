"""Local variable declaration placement and naming."""
import re

from .ast import (Assign, BinOp, Call, CallStmt, Closure, Concat, Const, GenFor, Global, If,
                  Index, LocalDecl, MethodCall, NumFor, RegDef, RegRef, Repeat, Return,
                  TableCons, UnOp, Upval, Vararg, While, deref)
from .cfg import DecompileError, SetList

KEYWORDS = {
    "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "if", "in",
    "local", "nil", "not", "or", "repeat", "return", "then", "true", "until", "while",
    "continue", "type", "export", "typeof",
}
BUILTINS = {
    "_G", "_VERSION", "assert", "collectgarbage", "error", "getfenv", "getmetatable", "ipairs",
    "load", "loadstring", "next", "newproxy", "pairs", "pcall", "print", "rawequal", "rawget",
    "rawlen", "rawset", "require", "select", "setfenv", "setmetatable", "tonumber", "tostring",
    "unpack", "xpcall", "bit32", "buffer", "coroutine", "debug", "math", "os", "string",
    "table", "utf8", "vector", "game", "workspace", "script", "plugin", "shared", "task",
    "wait", "delay", "spawn", "tick", "time", "warn", "elapsedTime", "settings", "stats",
    "version", "Enum", "Instance", "Vector2", "Vector3", "CFrame", "Color3", "UDim", "UDim2",
    "Rect", "Ray", "Region3", "BrickColor", "NumberRange", "NumberSequence", "ColorSequence",
    "TweenInfo", "DateTime", "Random", "Axes", "Faces", "PhysicalProperties", "Font",
    "Path2DControlPoint", "SharedTable", "OverlapParams", "RaycastParams", "UserSettings",
    "Workspace", "Game", "PluginManager", "DockWidgetPluginGuiInfo", "Content", "integer",
    "self", "_ENV", "arg",
}

_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


def is_identifier(s):
    return bool(_IDENT.match(s)) and s not in KEYWORDS - {"type", "export", "typeof"} \
        and s not in ("continue",)


def is_field_name(s):
    """Can `s` be used as `t.s` (Luau allows contextual keywords as field names)."""
    return bool(_IDENT.match(s)) and s not in {
        "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "if",
        "in", "local", "nil", "not", "or", "repeat", "return", "then", "true", "until",
        "while"}


# ----------------------------------------------------------- declarations
class _RefWalker:
    def __init__(self, fn):
        self.fn = fn
        self.blocks = {}
        self.decl = {}       # web -> path
        self.owned_open = set()
        self.owned = set()
        self.order = []
        self._seen = set()

    def ref(self, w, path):
        if w.is_param:
            return
        if w in self.owned:
            if w not in self.owned_open:
                raise DecompileError("loop variable used outside its loop")
            return
        cur = self.decl.get(w)
        if cur is None:
            self.decl[w] = list(path)
            if w not in self._seen:
                self._seen.add(w)
                self.order.append(w)
            return
        n = min(len(cur), len(path))
        m = 0
        while m < n and cur[m][0] == path[m][0]:
            m += 1
        if m == 0:
            raise DecompileError("scope analysis failed")
        if m < len(cur):
            del cur[m:]

    def expr(self, e, path):
        stack = [e]
        while stack:
            x = stack.pop()
            t = type(x)
            if t is RegRef:
                if x.repl is not None:
                    stack.append(x.repl)
                else:
                    self.ref(x.web, path)
            else:
                ch = x.children()
                if ch:
                    stack.extend(ch)

    def block(self, stmts, path):
        bid = id(stmts)
        self.blocks[bid] = stmts
        for idx, s in enumerate(stmts):
            p = path + [(bid, idx)]
            t = type(s)
            if t is Assign:
                for tg in s.targets:
                    tt = type(tg)
                    if tt is RegDef:
                        self.ref(tg.web, p)
                    elif tt is Index:
                        self.expr(tg.obj, p)
                        self.expr(tg.key, p)
                for v in s.values:
                    self.expr(v, p)
            elif t is CallStmt:
                self.expr(s.call, p)
            elif t is Return:
                for v in s.values:
                    self.expr(v, p)
            elif t is If:
                self.expr(s.cond, p)
                self.block(s.then, p)
                self.block(s.orelse, p)
            elif t is While:
                self.expr(s.cond, p)
                self.block(s.body, p)
            elif t is Repeat:
                self.block(s.body, p)
                self.expr(s.cond, p + [(id(s.body), len(s.body))])
            elif t is NumFor:
                for e in (s.start, s.limit, s.step):
                    self.expr(e, p)
                self._for_body([s.var], s.body, p)
            elif t is GenFor:
                for e in s.exprs:
                    self.expr(e, p)
                self._for_body(s.vars, s.body, p)
            elif t is SetList:
                self.expr(s.table, p)
                for v in s.values:
                    self.expr(v, p)

    def _for_body(self, vars_, body, p):
        # (a loop may legitimately appear twice when the structurer duplicated code)
        for v in vars_:
            if v in self.owned_open:
                raise DecompileError("loop variable reused by a nested loop")
            if v in self.decl:
                raise DecompileError("loop variable used outside its loop")
            self.owned.add(v)
            self.owned_open.add(v)
            if v not in self._seen:
                self._seen.add(v)
                self.order.append(v)
        self.block(body, p)
        for v in vars_:
            self.owned_open.discard(v)


def _rhs_refs(values, webs):
    found = set()
    for v in values:
        stack = [v]
        while stack:
            x = stack.pop()
            if type(x) is RegRef:
                if x.repl is not None:
                    stack.append(x.repl)
                elif x.web in webs:
                    found.add(x.web)
            else:
                stack.extend(x.children())
    return found


def place_declarations(fn, body, webs):
    w = _RefWalker(fn)
    w.block(body, [])
    root = id(body)
    # webs that may be read before being written must live at function scope
    for web in webs:
        if web.is_param or web.folded:
            continue
        if any(d[1] is None for d in web.defs) and web in w.decl:
            w.decl[web] = [(root, 0)]
    groups = {}
    for web, path in w.decl.items():
        bid, idx = path[-1]
        groups.setdefault((bid, idx), []).append(web)
    by_block = {}
    for (bid, idx), ws in groups.items():
        by_block.setdefault(bid, []).append((idx, ws))
    for bid, items in by_block.items():
        stmts = w.blocks[bid]
        for idx, ws in sorted(items, key=lambda x: -x[0]):
            ws.sort(key=lambda x: x.id)
            if idx < len(stmts):
                s = stmts[idx]
                if type(s) is Assign and all(type(t) is RegDef for t in s.targets):
                    tw = [t.web for t in s.targets]
                    if len(set(tw)) == len(tw) and set(tw) <= set(ws):
                        self_refs = _rhs_refs(s.values, set(tw))
                        ok = not self_refs
                        if not ok and len(tw) == 1 and len(s.values) == 1 \
                                and type(s.values[0]) is Closure and _closure_self_only(s.values[0], tw[0]):
                            ok = True
                            s.values[0].fn.local_function_name = True
                        if ok:
                            s.is_local = True
                            rest = [x for x in ws if x not in tw]
                            if rest:
                                stmts.insert(idx, LocalDecl(rest))
                            continue
            stmts.insert(idx, LocalDecl(ws))
    return w.order


def _closure_self_only(clo, web):
    for c in clo.captures:
        if type(c) is RegRef and c.web is web:
            continue
        if type(c) is RegRef and _rhs_refs([c], {web}):
            return False
    return True


# ------------------------------------------------------------------ naming
def _sanitize(s):
    s = re.sub(r"[^A-Za-z0-9_]", "_", s)
    s = s.strip("_") or ""
    if not s:
        return ""
    if s[0].isdigit():
        s = "_" + s
    if len(s) > 40:
        s = s[:40]
    return s


def _const_str(e):
    e = deref(e)
    if type(e) is Const and e.kind == "string":
        try:
            return e.value.decode("utf-8")
        except UnicodeDecodeError:
            return None
    return None


def _name_from_expr(e):
    e = deref(e)
    t = type(e)
    if t is Call:
        f = deref(e.func)
        if type(f) is Global and f.name == "require" and e.args:
            a = deref(e.args[0])
            if type(a) is Index:
                s = _const_str(a.key)
                if s:
                    return s
            return None
        if type(f) is Index:
            k = _const_str(f.key)
            if k == "new":
                o = deref(f.obj)
                if type(o) is Global and o.name == "Instance" and e.args:
                    return _const_str(e.args[0])
                if type(o) is Global:
                    return o.name[0].lower() + o.name[1:] if o.name else None
            return None
        return None
    if t is MethodCall:
        n = e.name.decode("utf-8", "replace")
        if n in ("GetService", "WaitForChild", "FindFirstChild", "FindFirstChildOfClass",
                 "FindFirstAncestor", "FindFirstChildWhichIsA", "FindFirstAncestorOfClass",
                 "FindFirstAncestorWhichIsA") and e.args:
            s = _const_str(e.args[0])
            if s:
                return s
        if n.startswith("Get") and len(n) > 3:
            return n[3:]
        return None
    if t is Index:
        return _const_str(e.key)
    if t is Global:
        return e.name
    if t is Closure:
        dn = e.fn.proto.debugname
        return dn
    if t is TableCons:
        return "tbl"
    return None


class Namer:
    def __init__(self, reserved):
        self.used = set(reserved)

    def take(self, hint):
        base = _sanitize(hint) if hint else ""
        if not base:
            base = "v"
        if base in KEYWORDS:
            base = base + "_"
        if base not in self.used:
            self.used.add(base)
            return base
        sep = "_" if base[-1].isdigit() else ""
        i = 1
        while True:
            n = "%s%s%d" % (base, sep, i)
            if n not in self.used:
                self.used.add(n)
                return n
            i += 1


def name_webs(fn, body, declared, reserved):
    namer = Namer(reserved)
    for i, pw in enumerate(fn.param_webs):
        pw.name = namer.take("self" if (i == 0 and fn.is_method) else "arg%d" % (i + 1))
    # loop variables get conventional names; collect from the AST in order
    loop_names = {}
    _collect_loop_names(body, loop_names, 0)
    for web in declared:
        if web.name is not None:
            continue
        hint = loop_names.get(web) or web.hint
        if hint is None:
            for s, rd in web.defs:
                if rd is not None and type(s) is Assign and len(s.values) == 1:
                    hint = _name_from_expr(s.values[0])
                    if hint:
                        break
        web.name = namer.take(hint)
    fn.names = namer.used
    return namer


def _collect_loop_names(stmts, out, depth):
    numeric = "ijklmn"
    for s in stmts:
        t = type(s)
        if t is NumFor:
            out[s.var] = numeric[depth] if depth < len(numeric) else "i"
            _collect_loop_names(s.body, out, depth + 1)
        elif t is GenFor:
            kind = None
            if len(s.exprs) == 1:
                e = deref(s.exprs[0])
                if type(e) is Call and type(deref(e.func)) is Global:
                    kind = deref(e.func).name
            names = (["i", "v"] if kind == "ipairs" else ["k", "v"])
            for i, v in enumerate(s.vars):
                out[v] = names[i] if i < 2 else "v%d" % (i + 1)
            _collect_loop_names(s.body, out, depth + 1)
        elif t is If:
            _collect_loop_names(s.then, out, depth)
            _collect_loop_names(s.orelse, out, depth)
        elif t is While or t is Repeat:
            _collect_loop_names(s.body, out, depth)


# ------------------------------------------------------- local count limit
def _max_active(stmts, active):
    """Max simultaneously active locals while executing `stmts` (Luau limit: 200)."""
    best = active
    cur = active
    for s in stmts:
        t = type(s)
        if t is LocalDecl:
            cur += len(s.webs)
        elif t is Assign and s.is_local:
            cur += len(s.targets)
        elif t is If:
            best = max(best, _max_active(s.then, cur), _max_active(s.orelse, cur))
        elif t is While or t is Repeat:
            best = max(best, _max_active(s.body, cur))
        elif t is NumFor:
            best = max(best, _max_active(s.body, cur + 1 + 3))
        elif t is GenFor:
            best = max(best, _max_active(s.body, cur + len(s.vars) + 3))
        best = max(best, cur)
    return best


def enforce_local_limit(fn, body, namer, limit=190):
    """Move function-scope locals into a table when the function would exceed
    Luau's local variable limit."""
    nparams = len(fn.param_webs) + (1 if fn.proto.is_vararg else 0)
    if _max_active(body, nparams) <= limit:
        return
    top = []
    for s in body:
        if type(s) is LocalDecl:
            top.extend(s.webs)
        elif type(s) is Assign and s.is_local:
            top.extend(t.web for t in s.targets)
    excess = _max_active(body, nparams) - limit + 1
    spilled = set(top[-excess:]) if excess < len(top) else set(top)
    if not spilled:
        raise DecompileError("too many local variables")
    holder = namer.take("spill")
    for w in spilled:
        w.name = holder + "." + w.name
    out = []
    for s in body:
        t = type(s)
        if t is LocalDecl:
            keep = [w for w in s.webs if w not in spilled]
            if keep:
                s.webs = keep
                out.append(s)
            continue
        if t is Assign and s.is_local:
            tw = [x.web for x in s.targets]
            if any(w in spilled for w in tw):
                keep = [w for w in tw if w not in spilled]
                if keep:
                    out.append(LocalDecl(keep))
                s.is_local = False
        out.append(s)
    from .ast import Raw
    body[:] = [Raw("local %s = {}" % holder)] + out
