"""Readability rewrites on the structured AST (all semantics-preserving)."""
from .ast import (Assign, BinOp, Break, Const, Continue, GenFor, If, NumFor, RegDef, RegRef,
                  Repeat, Return, UnOp, While, deref, iter_regrefs)
from .structure import negate

_CMP = {"==", "~=", "<", "<=", ">", ">="}


def _terminal(stmts):
    if not stmts:
        return False
    t = type(stmts[-1])
    return t is Break or t is Continue or t is Return


def _is_bool_const(e, val):
    e = deref(e)
    return type(e) is Const and e.kind == "bool" and e.value is val


def _single_regdef_assign(stmts):
    if len(stmts) == 1 and type(stmts[0]) is Assign and len(stmts[0].targets) == 1 \
            and type(stmts[0].targets[0]) is RegDef and len(stmts[0].values) == 1:
        return stmts[0]
    return None


def _is_boolean_expr(e):
    e = deref(e)
    if type(e) is UnOp and e.op == "not":
        return True
    if type(e) is BinOp and e.op in _CMP:
        return True
    if type(e) is BinOp and e.op in ("and", "or"):
        return _is_boolean_expr(e.a) and _is_boolean_expr(e.b)
    if type(e) is Const and e.kind == "bool":
        return True
    return False


def negate_value(e):
    """Negation of a boolean-valued expression in a *value* context: the
    result must stay a boolean with the same value."""
    e = deref(e)
    if type(e) is UnOp and e.op == "not" and _is_boolean_expr(e.a):
        return e.a
    if type(e) is BinOp and e.op in ("==", "~="):
        return BinOp("~=" if e.op == "==" else "==", e.a, e.b)
    if type(e) is BinOp and e.op in ("and", "or") and _is_boolean_expr(e.a) and _is_boolean_expr(e.b):
        return BinOp("or" if e.op == "and" else "and", negate_value(e.a), negate_value(e.b))
    if type(e) is Const and e.kind == "bool":
        return Const("bool", not e.value)
    return UnOp("not", e)


def _reads_web(e, web):
    e = deref(e)
    return type(e) is RegRef and e.repl is None and e.web is web


def has_continue(stmts):
    for s in stmts:
        t = type(s)
        if t is Continue:
            return True
        if t is If and (has_continue(s.then) or has_continue(s.orelse)):
            return True
    return False


def remove_tail_continue(stmts):
    if not stmts:
        return
    last = stmts[-1]
    if type(last) is Continue:
        stmts.pop()
    elif type(last) is If:
        remove_tail_continue(last.then)
        remove_tail_continue(last.orelse)


def simplify(stmts):
    out = []
    for s in stmts:
        t = type(s)
        if t is If:
            s.then = simplify(s.then)
            s.orelse = simplify(s.orelse)
            if not s.then and s.orelse:
                s.cond = negate(s.cond)
                s.then, s.orelse = s.orelse, []
            if s.orelse and _terminal(s.then):
                rest = s.orelse
                s.orelse = []
                out.append(s)
                out.extend(rest)
                continue
            if s.orelse and _terminal(s.orelse) and not _terminal(s.then):
                rest = s.then
                s.cond = negate(s.cond)
                s.then, s.orelse = s.orelse, []
                out.append(s)
                out.extend(rest)
                continue
            # x = cond and true/false pattern
            a = _single_regdef_assign(s.then)
            b = _single_regdef_assign(s.orelse)
            if a and b and a.targets[0].web is b.targets[0].web and _is_boolean_expr(s.cond):
                if _is_bool_const(a.values[0], True) and _is_bool_const(b.values[0], False):
                    out.append(Assign([a.targets[0]], [s.cond], a.pc))
                    continue
                if _is_bool_const(a.values[0], False) and _is_bool_const(b.values[0], True):
                    out.append(Assign([a.targets[0]], [negate_value(s.cond)], a.pc))
                    continue
            # x = a; if x then x = b end  ->  x = a and b
            if out and not s.orelse:
                prev = out[-1]
                th = _single_regdef_assign(s.then)
                if th is not None and type(prev) is Assign and len(prev.targets) == 1 \
                        and type(prev.targets[0]) is RegDef and len(prev.values) == 1 \
                        and prev.targets[0].web is th.targets[0].web:
                    w = th.targets[0].web
                    c = deref(s.cond)
                    op = None
                    if _reads_web(c, w):
                        op = "and"
                    elif type(c) is UnOp and c.op == "not" and _reads_web(c.a, w):
                        op = "or"
                    if op is not None and not any(r.web is w for r in iter_regrefs(th.values[0])):
                        prev.values = [BinOp(op, prev.values[0], th.values[0])]
                        continue
            out.append(s)
        elif t is While:
            s.body = simplify(s.body)
            remove_tail_continue(s.body)
            out.append(_loop_form(s))
        elif t is Repeat:
            s.body = simplify(s.body)
            out.append(s)
        elif t is NumFor or t is GenFor:
            s.body = simplify(s.body)
            remove_tail_continue(s.body)
            out.append(s)
        else:
            out.append(s)
    return out


def _loop_form(w):
    c = deref(w.cond)
    if not (type(c) is Const and c.kind == "bool" and c.value is True):
        return w
    body = w.body
    if body and type(body[0]) is If and not body[0].orelse and len(body[0].then) == 1 \
            and type(body[0].then[0]) is Break:
        return While(negate(body[0].cond), simplify(body[1:]))
    if body and type(body[-1]) is If and not body[-1].orelse and len(body[-1].then) == 1 \
            and type(body[-1].then[0]) is Break and not has_continue(body[:-1]):
        return Repeat(body[:-1], body[-1].cond)
    return w


# ------------------------------------------------------------ late inlining
from .ast import (Call, CallStmt, Closure, Concat, Const as _Const, Global, IfExpr, Index,
                  MethodCall, TableCons, Upval, Vararg)


def _count_refs(stmts, uses, defs):
    for s in stmts:
        t = type(s)
        if t is Assign:
            for tg in s.targets:
                if type(tg) is RegDef:
                    defs[tg.web] = defs.get(tg.web, 0) + 1
                elif type(tg) is Index:
                    _count_expr(tg.obj, uses)
                    _count_expr(tg.key, uses)
            for v in s.values:
                _count_expr(v, uses)
        elif t is CallStmt:
            _count_expr(s.call, uses)
        elif t is Return:
            for v in s.values:
                _count_expr(v, uses)
        elif t is If:
            _count_expr(s.cond, uses)
            _count_refs(s.then, uses, defs)
            _count_refs(s.orelse, uses, defs)
        elif t is While or t is Repeat:
            _count_expr(s.cond, uses)
            _count_refs(s.body, uses, defs)
        elif t is NumFor:
            for e in (s.start, s.limit, s.step):
                _count_expr(e, uses)
            defs[s.var] = defs.get(s.var, 0) + 1
            _count_refs(s.body, uses, defs)
        elif t is GenFor:
            for e in s.exprs:
                _count_expr(e, uses)
            for v in s.vars:
                defs[v] = defs.get(v, 0) + 1
            _count_refs(s.body, uses, defs)
        else:
            # SetList and others: count conservatively
            for name in ("table", "values"):
                x = getattr(s, name, None)
                if x is None:
                    continue
                for e in (x if isinstance(x, list) else [x]):
                    _count_expr(e, uses)


def _count_expr(e, uses):
    stack = [e]
    while stack:
        x = stack.pop()
        if type(x) is RegRef:
            if x.repl is not None:
                stack.append(x.repl)
            else:
                uses.setdefault(x.web, []).append(x)
        else:
            stack.extend(x.children())


def _is_import(e):
    while type(e) is Index:
        k = e.key
        while type(k) is RegRef and k.repl is not None:
            k = k.repl
        if type(k) is not _Const or k.kind != "string":
            return False
        e = e.obj
        while type(e) is RegRef and e.repl is not None:
            e = e.repl
    return type(e) is Global and e.imported


class _Unsafe(Exception):
    pass


def _first_use_safe(stmt, ref):
    """True if `ref` is evaluated (unconditionally, not captured) in `stmt`
    before anything with possible side effects."""
    state = {"impure": False}

    def ev(e, cond=False):
        e2 = e
        while type(e2) is RegRef and e2.repl is not None:
            e2 = e2.repl
        t = type(e2)
        if t is RegRef:
            if e2 is ref:
                if state["impure"] or cond:
                    raise _Unsafe()
                raise StopIteration
            return
        if t in (_Const, Global, Upval, Vararg):
            return
        if t is Closure:
            for c in e2.captures:
                if c is ref:
                    raise _Unsafe()
            return
        if t is Index:
            if _is_import(e2):
                return              # imports are load-time constants
            ev(e2.obj, cond)
            ev(e2.key, cond)
            state["impure"] = True
            return
        if t is Call:
            ev(e2.func, cond)
            for a in e2.args:
                ev(a, cond)
            state["impure"] = True
            return
        if t is MethodCall:
            ev(e2.obj, cond)
            for a in e2.args:
                ev(a, cond)
            state["impure"] = True
            return
        if t is BinOp:
            ev(e2.a, cond)
            if e2.op in ("and", "or"):
                ev(e2.b, True)
            else:
                ev(e2.b, cond)
                state["impure"] = True
            return
        if t is UnOp:
            ev(e2.a, cond)
            if e2.op != "not":
                state["impure"] = True
            return
        if t is Concat:
            for p in e2.parts:
                ev(p, cond)
            state["impure"] = True
            return
        if t is TableCons:
            for k, v in e2.items:
                if k is not None:
                    ev(k, cond)
                ev(v, cond)
            return
        if t is IfExpr:
            ev(e2.cond, cond)
            ev(e2.a, True)
            ev(e2.b, True)
            return
        raise _Unsafe()

    try:
        t = type(stmt)
        if t is Assign:
            for tg in stmt.targets:
                if type(tg) is Index:
                    ev(tg.obj)
                    ev(tg.key)
            for v in stmt.values:
                ev(v)
        elif t is CallStmt:
            ev(stmt.call)
        elif t is Return:
            for v in stmt.values:
                ev(v)
        elif t is If:
            ev(stmt.cond)
        elif t is NumFor:
            ev(stmt.start)
            ev(stmt.limit)
            ev(stmt.step)
        elif t is GenFor:
            for e in stmt.exprs:
                ev(e)
        return False
    except StopIteration:
        return True
    except _Unsafe:
        return False


def inline_single_use(body):
    uses = {}
    defs = {}
    _count_refs(body, uses, defs)
    _inline_block(body, uses, defs)


def _inline_block(stmts, uses, defs):
    for s in stmts:
        t = type(s)
        if t is If:
            _inline_block(s.then, uses, defs)
            _inline_block(s.orelse, uses, defs)
        elif t in (While, Repeat, NumFor, GenFor):
            _inline_block(s.body, uses, defs)
    i = len(stmts) - 2
    while i >= 0:
        s = stmts[i]
        if (type(s) is Assign and len(s.targets) == 1 and type(s.targets[0]) is RegDef
                and len(s.values) == 1):
            w = s.targets[0].web
            us = uses.get(w, ())
            if (len(us) == 1 and defs.get(w, 0) == 1 and not w.is_param
                    and w.for_owner is None and not getattr(w, "no_inline", False)):
                ref = us[0]
                nxt = stmts[i + 1]
                if _first_use_safe(nxt, ref) and not any(
                        r.web is w for r in iter_regrefs(s.values[0])):
                    ref.repl = s.values[0]
                    del stmts[i]
                    uses.pop(w, None)
                    defs.pop(w, None)
                    # the merged statement is now stmts[i]; try (stmts[i-1], stmts[i])
                    i -= 1
                    continue
        i -= 1
