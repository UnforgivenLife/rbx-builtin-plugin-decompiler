"""Expression / statement nodes used by the decompiler."""


# ---------------------------------------------------------------- expressions
class Expr:
    __slots__ = ()
    # number of values produced: 1 for ordinary expressions; calls/varargs carry nret
    def children(self):
        return ()


class Const(Expr):
    __slots__ = ("value", "kind")
    # kind: 'nil' 'bool' 'number' 'string' 'vector' 'integer'

    def __init__(self, kind, value=None):
        self.kind = kind
        self.value = value


class Global(Expr):
    __slots__ = ("name", "imported")

    def __init__(self, name, imported=False):
        self.name = name
        self.imported = imported


class RegRef(Expr):
    """A read of a virtual register. After data-flow analysis `web` is set;
    after folding `repl` may hold the inlined expression."""
    __slots__ = ("reg", "web", "repl", "nofold", "stmt")

    def __init__(self, reg, nofold=False):
        self.reg = reg
        self.web = None
        self.repl = None
        self.nofold = nofold
        self.stmt = None


class Upval(Expr):
    __slots__ = ("index", "fn")

    def __init__(self, index, fn):
        self.index = index
        self.fn = fn  # FunctionInfo owning the upvalue


class Index(Expr):
    __slots__ = ("obj", "key")

    def __init__(self, obj, key):
        self.obj = obj
        self.key = key

    def children(self):
        return (self.obj, self.key)


class Call(Expr):
    __slots__ = ("func", "args", "nret")

    def __init__(self, func, args, nret):
        self.func = func
        self.args = args
        self.nret = nret  # -1 = multret

    def children(self):
        return (self.func,) + tuple(self.args)


class MethodCall(Expr):
    __slots__ = ("obj", "name", "args", "nret")

    def __init__(self, obj, name, args, nret):
        self.obj = obj
        self.name = name
        self.args = args
        self.nret = nret

    def children(self):
        return (self.obj,) + tuple(self.args)


class Vararg(Expr):
    __slots__ = ("nret",)

    def __init__(self, nret):
        self.nret = nret


class BinOp(Expr):
    __slots__ = ("op", "a", "b")

    def __init__(self, op, a, b):
        self.op = op
        self.a = a
        self.b = b

    def children(self):
        return (self.a, self.b)


class UnOp(Expr):
    __slots__ = ("op", "a")

    def __init__(self, op, a):
        self.op = op
        self.a = a

    def children(self):
        return (self.a,)


class Concat(Expr):
    __slots__ = ("parts",)

    def __init__(self, parts):
        self.parts = parts

    def children(self):
        return tuple(self.parts)


class TableCons(Expr):
    # items: list of (key_expr_or_None, value_expr)
    # committed/closed/moved: constructor-merging state used by fold.py
    __slots__ = ("items", "committed", "closed", "moved")

    def __init__(self, items=None):
        self.items = items or []
        self.committed = 0
        self.closed = False
        self.moved = set()

    def children(self):
        out = []
        for k, v in self.items:
            if k is not None:
                out.append(k)
            out.append(v)
        return tuple(out)


class IfExpr(Expr):
    __slots__ = ("cond", "a", "b")

    def __init__(self, cond, a, b):
        self.cond = cond
        self.a = a
        self.b = b

    def children(self):
        return (self.cond, self.a, self.b)


class Closure(Expr):
    __slots__ = ("fn", "captures")  # captures: list of Expr (RegRef / Upval)

    def __init__(self, fn, captures):
        self.fn = fn
        self.captures = captures

    def children(self):
        return tuple(self.captures)


class Name(Expr):
    """Already-resolved local variable reference (used by the fallback emitter)."""
    __slots__ = ("name",)

    def __init__(self, name):
        self.name = name


def deref(e):
    while type(e) is RegRef and e.repl is not None:
        e = e.repl
    return e


def iter_regrefs(e):
    """Yield RegRefs inside expression `e` in evaluation order (not following repl)."""
    stack = [e]
    out = []
    while stack:
        x = stack.pop()
        t = type(x)
        if t is RegRef:
            if x.repl is not None:
                stack.append(x.repl)
            else:
                out.append(x)
        else:
            ch = x.children()
            if ch:
                stack.extend(reversed(ch))
    return out


def multi_value(e):
    e = deref(e)
    t = type(e)
    return (t is Call or t is MethodCall or t is Vararg) and e.nret == -1


# ----------------------------------------------------------------- statements
class Stmt:
    __slots__ = ()


class RegDef:
    """Assignment target that is a register."""
    __slots__ = ("reg", "web")

    def __init__(self, reg):
        self.reg = reg
        self.web = None


class Assign(Stmt):
    __slots__ = ("targets", "values", "is_local", "pc")
    # targets: RegDef | Global | Index | Upval

    def __init__(self, targets, values, pc=-1):
        self.targets = targets
        self.values = values
        self.is_local = False
        self.pc = pc


class CallStmt(Stmt):
    __slots__ = ("call", "pc")

    def __init__(self, call, pc=-1):
        self.call = call
        self.pc = pc


class Return(Stmt):
    __slots__ = ("values", "pc")

    def __init__(self, values, pc=-1):
        self.values = values
        self.pc = pc


class LocalDecl(Stmt):
    __slots__ = ("webs",)

    def __init__(self, webs):
        self.webs = webs


class If(Stmt):
    __slots__ = ("cond", "then", "orelse")

    def __init__(self, cond, then, orelse):
        self.cond = cond
        self.then = then
        self.orelse = orelse


class While(Stmt):
    __slots__ = ("cond", "body")

    def __init__(self, cond, body):
        self.cond = cond
        self.body = body


class Repeat(Stmt):
    __slots__ = ("body", "cond")

    def __init__(self, body, cond):
        self.body = body
        self.cond = cond


class NumFor(Stmt):
    __slots__ = ("var", "start", "limit", "step", "body")

    def __init__(self, var, start, limit, step, body):
        self.var = var
        self.start = start
        self.limit = limit
        self.step = step
        self.body = body


class GenFor(Stmt):
    __slots__ = ("vars", "exprs", "body")

    def __init__(self, vars_, exprs, body):
        self.vars = vars_
        self.exprs = exprs
        self.body = body


class Break(Stmt):
    __slots__ = ()


class Continue(Stmt):
    __slots__ = ()


class Do(Stmt):
    __slots__ = ("body",)

    def __init__(self, body):
        self.body = body


class Comment(Stmt):
    __slots__ = ("text",)

    def __init__(self, text):
        self.text = text


class Raw(Stmt):
    __slots__ = ("text",)

    def __init__(self, text):
        self.text = text
