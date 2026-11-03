"""Recovery of value-producing conditionals at CFG level.

    X: ...; if r then goto M          X: ...; r = r or b      (and `and` for JUMPIFNOT)
    T: r = b                    ==>    M: ...
    M: ...

    X: ...; if c then goto T else F   X: ...; r = if c then a else b
    T: r = a; goto M            ==>    M: ...
    F: r = b; goto M

After each rewrite X is merged with M when possible and re-folded, so the new
expression can be inlined into its consumer (call arguments, constructors...).
"""
from .ast import Assign, BinOp, IfExpr, RegDef, RegRef, UnOp, deref
from .cfg import Term
from .dataflow import Web
from .fold import fold_block
from .passes import _is_boolean_expr, negate_value


def _is_bool(e, v):
    return type(e).__name__ == "Const" and e.kind == "bool" and e.value is v


def _single_assign(b):
    """Block containing exactly `r = expr` (one register target) and a jump."""
    if len(b.stmts) != 1 or b.term.kind != "jump":
        return None
    s = b.stmts[0]
    if type(s) is not Assign or len(s.targets) != 1 or type(s.targets[0]) is not RegDef \
            or len(s.values) != 1:
        return None
    return s


class TernaryRecovery:
    def __init__(self, rpo, webs):
        self.blocks = rpo
        self.webs = webs
        self.dead = set()
        self.back_targets = set()
        for b in rpo:
            for s in b.succs:
                if s.start <= b.start:
                    self.back_targets.add(s.id)
        self._next_web = -1

    def run(self):
        changed = True
        while changed:
            changed = False
            for X in self.blocks:
                if X.id in self.dead or X.term is None or X.term.kind != "cond":
                    continue
                if self.try_andor(X) or self.try_ifexpr(X):
                    changed = True
        return [b for b in self.blocks if b.id not in self.dead]

    # ------------------------------------------------------------ helpers
    def _ok_target(self, b, X):
        return b.id not in self.back_targets and b.start > X.start and b.term.kind not in (
            "fornloop", "forgloop")

    def _replace_pred(self, blk, old, new):
        ps = [p for p in blk.preds if p is not old]
        if new is not None and new not in ps:
            ps.append(new)
        blk.preds = ps

    def _finish(self, X, M, removed):
        for r in removed:
            self.dead.add(r.id)
            for s in r.succs:
                s.preds = [p for p in s.preds if p is not r]
        t = Term("jump", X.term.pc)
        X.term = t
        X.succs = [M]
        if X not in M.preds:
            M.preds.append(X)
        # merge X and M when M is only reachable from X
        if len(M.preds) == 1 and M.preds[0] is X and self._ok_target(M, X) and M.id not in self.dead:
            X.stmts = X.stmts + M.stmts
            X.term = M.term
            X.succs = M.succs
            X.end = M.end
            for s in M.succs:
                s.preds = [X if p is M else p for p in s.preds]
            self.dead.add(M.id)
        fold_block(X)

    def _new_web(self):
        w = Web(self._next_web)
        self._next_web -= 1
        self.webs.append(w)
        return w

    # --------------------------------------------------------- patterns
    def try_andor(self, X):
        c = deref(X.term.cond)
        if type(c) is RegRef and c.repl is None:
            ref, op = c, "or"
        elif type(c) is UnOp and c.op == "not" and type(c.a) is RegRef and c.a.repl is None:
            ref, op = c.a, "and"
        else:
            return False
        M, T = X.succs
        if T is M or len(T.preds) != 1 or T.id in self.back_targets or T.start <= X.start:
            return False
        s = _single_assign(T)
        if s is None or T.succs[0] is not M:
            return False
        rdT = s.targets[0]
        w = ref.web
        if rdT.reg != ref.reg or rdT.web is not w or len(w.defs) != 2:
            return False
        # the value tested must come from the last definition of the register in X
        D1 = None
        for st in reversed(X.stmts):
            if type(st) is Assign and any(type(t) is RegDef and t.reg == ref.reg for t in st.targets):
                D1 = st
                break
        if D1 is None or len(D1.targets) != 1 or D1.targets[0].web is not w:
            return False
        if not any(d[0] is D1 for d in w.defs) or not any(d[0] is s for d in w.defs):
            return False
        # split: D1 gets its own single-use web feeding the new expression
        w1 = self._new_web()
        rd1 = D1.targets[0]
        rd1.web = w1
        w1.defs = [(D1, rd1)]
        nref = RegRef(ref.reg)
        nref.web = w1
        w1.uses = [nref]
        w1.nuses = 1
        rd = RegDef(ref.reg)
        rd.web = w
        new = Assign([rd], [BinOp(op, nref, s.values[0])], s.pc)
        nref.stmt = new
        w.defs = [(new, rd)]
        w.uses = [u for u in w.uses if u is not ref]
        w.nuses -= 1
        X.stmts.append(new)
        self._finish(X, M, [T])
        return True

    def try_ifexpr(self, X):
        T, F = X.succs
        if T is F:
            return False
        for b in (T, F):
            if len(b.preds) != 1 or b.id in self.back_targets or b.start <= X.start:
                return False
        sT = _single_assign(T)
        sF = _single_assign(F)
        if sT is None or sF is None:
            return False
        M = T.succs[0]
        if F.succs[0] is not M or M is X:
            return False
        rT = sT.targets[0]
        rF = sF.targets[0]
        w = rT.web
        if rT.reg != rF.reg or rF.web is not w or len(w.defs) != 2:
            return False
        rd = RegDef(rT.reg)
        rd.web = w
        a, b = deref(sT.values[0]), deref(sF.values[0])
        cond = X.term.cond
        if _is_bool(a, True) and _is_bool(b, False) and _is_boolean_expr(cond):
            val = cond                       # x = a < b
        elif _is_bool(a, False) and _is_bool(b, True) and _is_boolean_expr(cond):
            val = negate_value(cond)         # x = not (a < b)
        else:
            val = IfExpr(cond, sT.values[0], sF.values[0])
        new = Assign([rd], [val], sT.pc)
        w.defs = [(new, rd)]
        X.stmts.append(new)
        self._finish(X, M, [T, F])
        return True
