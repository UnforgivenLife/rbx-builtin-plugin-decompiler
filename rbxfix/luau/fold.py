"""Expression folding: inline single-use temporaries into their consumers and
rebuild table constructors.

Correctness argument: a definition is only inlined when it is the most recent
not-yet-emitted statement and the operand it feeds is the latest-evaluated
remaining operand of the consumer, so evaluation order is preserved exactly.
"""
from .ast import (Assign, BinOp, Call, CallStmt, Closure, Const, Global, Index, MethodCall, RegDef, RegRef, UnOp,
                  TableCons, Upval, Vararg, deref, iter_regrefs)
from .cfg import MULT, NOFOLD, PUREFOLD, SetList, Term, CloseUpvals, DecompileError
from .dataflow import stmt_uses


def _is_pure(e):
    e = deref(e)
    t = type(e)
    if t is Const or t is Global or t is Upval or t is Closure:
        return True
    if t is RegRef:
        return True
    return False


def _deep_pure(e):
    """No side effects and cannot raise (constants, variable reads, closures,
    constructors of such)."""
    e = deref(e)
    t = type(e)
    if t is Const or t is Upval or t is Global or t is Closure:
        return True
    if t is RegRef:
        return True
    if t is TableCons:
        for k, v in e.items:
            if (k is not None and not _deep_pure(k)) or not _deep_pure(v):
                return False
            if k is not None and type(deref(k)) is Const and deref(k).kind == "nil":
                return False
        return True
    return False


def _is_import(e):
    e = deref(e)
    while type(e) is Index:
        k = deref(e.key)
        if type(k) is not Const or k.kind != "string":
            return False
        e = deref(e.obj)
    return type(e) is Global and getattr(e, "imported", False)


def _single_def_stmt(w):
    if len(w.defs) != 1 or w.is_param:
        return None
    s, rd = w.defs[0]
    if type(s) is not Assign or len(s.targets) != 1 or len(s.values) != 1 or rd is None:
        return None
    return s


def _refs_web(exprs, web):
    for e in exprs:
        for r in iter_regrefs(e):
            if r.web is web:
                return True
    return False


def fold_block(b):
    pending = []

    def eligible(u):
        w = u.web
        if u.nofold == NOFOLD or w.nuses != 1:
            return None
        d = _single_def_stmt(w)
        if d is None:
            return None
        if u.nofold == PUREFOLD and not _is_pure(d.values[0]):
            return None
        return d

    def try_fold(ops, func_ref=None):
        # For builtin calls (FASTCALL) the compiler loads the function *after* the
        # arguments, from an import, an upvalue or a local that it knows is never
        # reassigned.  Such a load is order-independent: let it float.
        if func_ref is not None and func_ref.repl is None and pending:
            top = pending[-1]
            if eligible(func_ref) is top and func_ref is not ops[-1]:
                v = deref(top.values[0])
                if _is_import(v) or type(v) is Upval or (type(v) is RegRef and v.repl is None):
                    pending.pop()
                    func_ref.repl = top.values[0]
                    func_ref.web.folded = True
        for u in reversed(ops):
            if u.repl is not None:
                continue
            d = eligible(u)
            if d is None:
                if u.reg == MULT:
                    raise DecompileError("could not place multi-value expression")
                continue
            if pending and pending[-1] is d:
                pending.pop()
                u.repl = d.values[0]
                u.web.folded = True
            elif any(p is d for p in pending):
                if u.reg == MULT:
                    raise DecompileError("multi-value expression out of order")
                break
            else:
                if u.reg == MULT:
                    raise DecompileError("multi-value expression not in block")
                continue

    def cons_of(stmt):
        if type(stmt) is Assign and len(stmt.values) == 1 and type(stmt.values[0]) is TableCons:
            return stmt.values[0]
        return None

    def table_def(tref):
        """The constructor statement defining the table register read by `tref`:
        the most recent definition of that register still pending in this block."""
        if type(tref) is not RegRef or tref.repl is not None:
            return None, None
        reg = tref.reg
        for d in reversed(pending):
            if type(d) is Assign and any(type(t) is RegDef and t.reg == reg for t in d.targets):
                if len(d.targets) != 1 or d.targets[0].web is not tref.web:
                    return None, None
                tc = cons_of(d)
                if tc is None:
                    return None, None
                return d, tc
        return None, None

    def purge_dead():
        keep = [p for p in pending if not (
            type(p) is Assign and len(p.targets) == 1 and type(p.targets[0]) is RegDef
            and p.targets[0].web.nuses == 0 and len(p.values) == 1 and _deep_pure(p.values[0]))]
        if len(keep) != len(pending):
            pending[:] = keep

    def sink_cons(d, tc, w):
        """Move constructor statement d to the top of `pending`: valid when the
        constructor only has constant contents (evaluation order is invisible)
        and nothing pending after it refers to the table."""
        if pending[-1] is d:
            return True
        for k, v in tc.items:
            if type(deref(v)) is not Const or (k is not None and type(deref(k)) is not Const):
                return False
        idx = len(pending) - 1
        while idx >= 0 and pending[idx] is not d:
            for r in stmt_uses(pending[idx]):
                if r.web is w:
                    return False
            idx -= 1
        if idx < 0:
            return False
        del pending[idx]
        pending.append(d)
        return True

    def try_merge(S):
        t = type(S)
        if t is Assign:
            if len(S.targets) != 1 or type(S.targets[0]) is not Index:
                return False
            tgt = S.targets[0]
            d, tc = table_def(tgt.obj)
            if d is None:
                return False
            st = tc
            if st.closed:
                return False
            w = tgt.obj.web
            if _refs_web([tgt.key, S.values[0]], w):
                return False
            # find d in pending; entries above it must be array temps for a SETLIST of w
            if not pending:
                return False
            if pending[-1] is not d:
                purge_dead()
            idx = len(pending) - 1
            while idx >= 0 and pending[idx] is not d:
                idx -= 1
            if idx < 0:
                return False
            above = pending[idx + 1:]
            moved = []
            if above:
                sl = None
                for a in above:
                    if type(a) is not Assign or len(a.targets) != 1 or type(a.targets[0]) is not RegDef:
                        return False
                    aw = a.targets[0].web
                    if aw.nuses != 1 or len(aw.defs) != 1 or len(a.values) != 1:
                        return False
                    use = aw.uses[0]
                    if type(use.stmt) is not SetList or use.stmt.table.web is not w:
                        return False
                    if sl is None:
                        sl = use.stmt
                    elif sl is not use.stmt:
                        return False
                    moved.append((a, use))
                # moved temps must be the leading values of that SETLIST, in order
                if sl.start != st.committed + 1:
                    return False
                off = len(st.moved)
                for i, (a, use) in enumerate(moved):
                    if off + i >= len(sl.values) or sl.values[off + i] is not use:
                        return False
                    if use.reg == MULT:
                        return False
            for a, use in moved:
                tc.items.append((None, a.values[0]))
                use.repl = a.values[0]
                use.web.folded = True
                st.moved.add(id(use))
            del pending[idx + 1:]
            tc.items.append((tgt.key, S.values[0]))
            w.nuses -= 1
            return True
        if t is SetList:
            d, tc = table_def(S.table)
            if d is not None and pending and pending[-1] is not d:
                purge_dead()
                sink_cons(d, tc, S.table.web)
            if d is None or not pending or pending[-1] is not d:
                return False
            st = tc
            if st.closed:
                return False
            nmoved = sum(1 for v in S.values if id(v) in st.moved)
            if S.start != st.committed + 1:
                return False
            w = S.table.web
            for v in S.values:
                if id(v) in st.moved:
                    continue
                if v.repl is None and v.web is w:
                    return False
            if _refs_web([v for v in S.values if id(v) not in st.moved], w):
                return False
            for v in S.values:
                if id(v) in st.moved:
                    continue
                tc.items.append((None, v.repl if v.repl is not None else v))
            st.committed += len(S.values)
            st.moved = set()
            if S.values and S.values[-1].reg == MULT:
                st.closed = True
            w.nuses -= 1
            return True
        return False

    for S in b.stmts:
        if type(S) is CloseUpvals:
            continue
        ops = stmt_uses(S)
        call = None
        if type(S) is CallStmt:
            call = S.call
        elif type(S) is Assign and len(S.values) == 1 and type(S.values[0]) is Call:
            call = S.values[0]
        fref = call.func if type(call) is Call and type(call.func) is RegRef else None
        try_fold(ops, fref)
        if try_merge(S):
            continue
        if (type(S) is Assign and len(S.targets) == 1 and type(S.targets[0]) is RegDef
                and S.targets[0].web.nuses == 0 and len(S.values) == 1 and _deep_pure(S.values[0])):
            continue  # dead, side-effect free definition (left over from inlining)
        pending.append(S)

    term = b.term
    if term is not None and term.kind not in ("jump", "return"):
        if term.kind in ("fornprep", "forgprep"):
            _fold_for(term, pending, eligible)
        else:
            _orient_compare(term.cond, pending, eligible)
            try_fold(stmt_uses(term))
    b.stmts = pending


def _fold_for(term, pending, eligible):
    uses = term.uses
    if term.kind == "forgprep" and pending:
        top = pending[-1]
        # `for ... in f(x) do` : one call producing the 3 iterator values
        if (type(top) is Assign and len(top.targets) == 3 and len(top.values) == 1
                and all(type(t) is RegDef for t in top.targets)):
            ok = True
            for t, u in zip(top.targets, uses):
                if t.web is not u.web or u.web.nuses != 1 or len(u.web.defs) != 1:
                    ok = False
            if ok:
                pending.pop()
                for u in uses:
                    u.web.folded = True
                term.cond = top.values[0]  # store multi-value iterator expression
                for u in uses:
                    u.repl = Const("nil")  # placeholder, not emitted
                return
    remaining = [u for u in uses if u.repl is None]
    while pending and remaining:
        top = pending[-1]
        hit = None
        for u in remaining:
            if eligible(u) is top:
                hit = u
                break
        if hit is None:
            break
        pending.pop()
        hit.repl = top.values[0]
        hit.web.folded = True
        remaining.remove(hit)


_SWAP = {"<": ">", "<=": ">="}


def _orient_compare(cond, pending, eligible):
    """`a > b` is compiled as LT(b, a) with `a` evaluated first.  When both
    operand temporaries are pending in that order, restore `a > b` so they can
    be inlined with their original evaluation order."""
    c = cond
    if type(c) is UnOp and c.op == "not":
        c = c.a
    if type(c) is not BinOp or c.op not in _SWAP or len(pending) < 2:
        return
    L, R = c.a, c.b
    if type(L) is not RegRef or type(R) is not RegRef or L.repl is not None or R.repl is not None:
        return
    if eligible(L) is pending[-1] and eligible(R) is pending[-2]:
        c.op = _SWAP[c.op]
        c.a, c.b = R, L
