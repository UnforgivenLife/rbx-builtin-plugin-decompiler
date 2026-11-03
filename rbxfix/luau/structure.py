"""Control-flow structuring: CFG of folded blocks -> structured AST.

Luau emits code in source order, so loops occupy contiguous pc ranges whose
exit ("follow") is the instruction right after the loop.  Conditionals are
structured with immediate post-dominators computed on per-loop region graphs
(inner loops collapsed to single nodes).  In those graphs `continue` edges lead
to a virtual exit while `break`/early `return` paths are dead ends, which makes
the join point of `if c then return end` the code after it.
"""
from .ast import (Assign, BinOp, Break, Call, Const, Continue, GenFor, If, MethodCall, NumFor,
                  RegDef, RegRef, UnOp, Vararg, While, deref, multi_value)
from .dataflow import Web
from .cfg import DecompileError

VEXIT = -1
DEAD = -2


class Loop:
    __slots__ = ("header", "kind", "latch", "end", "follow", "prep", "parent", "children",
                 "start", "active", "depth", "exits", "brk", "brk_done", "zone", "flag")

    def __init__(self, header, kind, latch, end):
        self.header = header
        self.kind = kind
        self.latch = latch
        self.end = end
        self.start = header.start
        self.follow = None
        self.prep = None
        self.parent = None
        self.children = []
        self.active = False
        self.depth = 0
        self.exits = []
        self.brk = None
        self.brk_done = False
        self.zone = set()
        self.flag = None

    def contains(self, b):
        return self.start <= b.start < self.end

    def __repr__(self):
        return "Loop(%s,%d..%d)" % (self.kind, self.start, self.end)


_NEG = {"==": "~=", "~=": "=="}


def negate(e):
    """Negation for *condition* contexts (only truthiness matters)."""
    e = deref(e)
    if type(e) is UnOp and e.op == "not":
        return e.a
    if type(e) is BinOp and e.op in _NEG:
        return BinOp(_NEG[e.op], e.a, e.b)
    if type(e) is BinOp and e.op in ("and", "or"):
        # De Morgan: exact for truthiness, same short-circuit order
        return BinOp("or" if e.op == "and" else "and", negate(e.a), negate(e.b))
    if type(e) is Const and e.kind == "bool":
        return Const("bool", not e.value)
    return UnOp("not", e)


class Structurer:
    def __init__(self, blocks_rpo):
        self.entry = min(blocks_rpo, key=lambda b: b.rpo)
        self.blocks = sorted(blocks_rpo, key=lambda b: b.start)
        self.reach = {b.id for b in self.blocks}
        self.emitted = {}
        self.budget = 16 * len(self.blocks) + 2000
        self._bid = {b.id: b for b in self.blocks}

    # ---------------------------------------------- compound conditions
    def collapse_conditions(self):
        back_targets = set()
        for b in self.blocks:
            for s in b.succs:
                if s.start <= b.start:
                    back_targets.add(s.id)
        changed = True
        while changed:
            changed = False
            for X in reversed(self.blocks):
                if X.id not in self.reach or X.term is None or X.term.kind != "cond":
                    continue
                for yi in (0, 1):
                    Y = X.succs[yi]
                    if (Y is X or Y.id in back_targets or Y.stmts or Y.term is None
                            or Y.term.kind != "cond" or len(Y.preds) != 1 or Y.preds[0] is not X
                            or Y.start <= X.start):
                        continue
                    Z = X.succs[1 - yi]
                    if Z is Y:
                        continue
                    c1 = X.term.cond
                    c2 = Y.term.cond
                    T2, F2 = Y.succs
                    if yi == 0:      # X: if c1 goto Y else Z
                        if F2 is Z:
                            cond, t, f = BinOp("and", c1, c2), T2, Z
                        elif T2 is Z:
                            cond, t, f = BinOp("and", c1, negate(c2)), F2, Z
                        else:
                            continue
                    else:            # X: if c1 goto Z else Y
                        if T2 is Z:
                            cond, t, f = BinOp("or", c1, c2), Z, F2
                        elif F2 is Z:
                            cond, t, f = BinOp("or", c1, negate(c2)), Z, T2
                        else:
                            continue
                    if t is f:
                        continue
                    X.term.cond = cond
                    X.succs = [t, f]
                    for s in (T2, F2):
                        s.preds = [p for p in s.preds if p is not Y]
                        if X not in s.preds:
                            s.preds.append(X)
                    self.reach.discard(Y.id)
                    changed = True
                    break
        self.blocks = [b for b in self.blocks if b.id in self.reach]

    # ------------------------------------------------------------ loops
    def find_loops(self):
        loops = []
        groups = {}
        by_start = {b.start: b for b in self.blocks}
        for b in self.blocks:
            k = b.term.kind if b.term is not None else None
            for i, s in enumerate(b.succs):
                if s.start > b.start:
                    continue
                if k in ("fornloop", "forgloop"):
                    if i != 0:
                        raise DecompileError("backward for-loop exit")
                    loops.append(Loop(s, "fornum" if k == "fornloop" else "forgen", b, b.end))
                else:
                    g = groups.get(s.id)
                    if g is None:
                        g = groups[s.id] = Loop(s, "while", b, b.end)
                        loops.append(g)
                    elif b.end > g.end:
                        g.end = b.end
                        g.latch = b
        for L in loops:
            f = by_start.get(L.end)
            L.follow = f if f is not None and f.id in self.reach else None
            if L.kind == "fornum":
                prep = None
                for p in L.header.preds:
                    if p.term is not None and p.term.kind == "fornprep" and p.end == L.header.start:
                        prep = p
                if prep is None:
                    raise DecompileError("numeric for loop without FORNPREP")
                if L.follow is not None and self.resolve(prep.succs[1]) is not self.resolve(L.follow):
                    raise DecompileError("numeric for loop exit mismatch")
                L.prep = prep
            elif L.kind == "forgen":
                prep = None
                for p in L.latch.preds:
                    if p.term is not None and p.term.kind == "forgprep" and p.end == L.header.start:
                        prep = p
                if prep is None:
                    raise DecompileError("generic for loop without FORGPREP")
                L.prep = prep
        loops.sort(key=lambda L: (L.start, -L.end, 0 if L.kind != "while" else 1))
        for L in loops:
            for M in loops:
                if L is not M and L.start < M.start < L.end < M.end:
                    raise DecompileError("overlapping loops")
        stack = []
        for L in loops:
            while stack and not (stack[-1].start <= L.start and L.end <= stack[-1].end):
                stack.pop()
            if stack:
                L.parent = stack[-1]
                L.depth = L.parent.depth + 1
                L.parent.children.append(L)
            stack.append(L)
        self.loops = loops
        self.loop_of = {}
        for b in self.blocks:
            inner = None
            for L in loops:
                if L.contains(b) and (inner is None or L.depth > inner.depth):
                    inner = L
            self.loop_of[b.id] = inner
        self.headers = {}
        for L in loops:
            if L.kind == "while":
                self.headers.setdefault(L.header.id, []).append(L)
        self.prep_loop = {L.prep.id: L for L in loops if L.prep is not None}
        self.loop_by_key = {("L", id(L)): L for L in loops}
        self._ipdom_cache = {}
        # exits of every loop: successors outside its pc range (+ natural exit)
        for L in loops:
            ex = []
            seen = set()
            for b in self.blocks:
                if not L.contains(b):
                    continue
                for s in b.succs:
                    if not L.contains(s) and s.id not in seen:
                        seen.add(s.id)
                        ex.append(s)
            if L.kind != "while" and L.follow is not None and L.follow.id not in seen:
                ex.append(L.follow)
            L.exits = ex
            L.brk = None
            L.brk_done = False
            L.zone = set()

    def resolve(self, b):
        """Skip over empty blocks that only jump forward (jump threading)."""
        n = 0
        while b is not None and not b.stmts and b.term.kind == "jump" and n < 64:
            nb = b.succs[0]
            if nb.start <= b.start or nb.id in getattr(self, "_header_ids", ()):
                break
            b = nb
            n += 1
        return b

    def loop_brk(self, L):
        """Structural follow of loop L: where control continues after all its exits."""
        if L.brk_done:
            return L.brk
        L.brk_done = True
        parent = L.parent
        f = self._ipdom_of(("L", id(L)), parent)
        F = None
        if f is not None and f != VEXIT:
            if isinstance(f, tuple):
                M = self.loop_by_key[f]
                F = M.prep if M.prep is not None else M.header
            else:
                F = self._bid.get(f)
        if F is None:
            targets = {}
            for e in L.exits:
                r = self.resolve(e)
                targets[r.id] = r
            if len(targets) == 1:
                # single exit, possibly jump-threaded straight to an outer loop's
                # exit/continue target: the parent region then sees it right after
                F = next(iter(targets.values()))
            else:
                F = L.follow
        L.brk = F
        # exit zone: code reachable from the exits before reaching F
        zone = set()
        # (for numeric/generic loops the natural exit path is emitted after the
        # loop, guarded by a flag if needed, so it is not part of the zone)
        work = [e for e in L.exits if e is not F and not (L.kind != "while" and e is L.follow)]
        while work:
            b = work.pop()
            if b is F or b.id in zone:
                continue
            v = self._vertex(b, parent)
            if not isinstance(v, int) or v < 0:
                continue
            zone.add(b.id)
            if b.term.kind in ("fornprep", "forgprep"):
                raise DecompileError("loop inside loop exit path")
            for s in b.succs:
                work.append(s)
        L.zone = zone
        return F

    # --------------------------------------------------- region pdom
    def _vertex(self, b, region):
        if region is not None:
            if region.kind == "while" and b is region.header:
                return VEXIT                      # continue
            if region.kind != "while" and b is region.latch:
                return VEXIT                      # continue
            if b is region.follow or not region.contains(b):
                return DEAD                       # break / leaving the loop
        L = self.loop_of.get(b.id)
        if L is region:
            return b.id
        C = L
        while C is not None and C.parent is not region:
            C = C.parent
        if C is None:
            return DEAD
        return ("L", id(C))

    def _region_graph(self, region, dead_exits):
        succ = {}
        nodes = [b for b in self.blocks if self.loop_of.get(b.id) is region]
        last_ret = None
        for b in nodes:
            if b.term.kind == "return" and (last_ret is None or b.start > last_ret.start):
                last_ret = b
        for b in nodes:
            t = b.term
            if t.kind in ("fornprep", "forgprep"):
                out = [("L", id(self.prep_loop[b.id]))]
            elif t.kind == "return":
                out = [VEXIT] if (dead_exits is False or (region is None and b is last_ret)) else []
            else:
                out = []
                for s in b.succs:
                    v = self._vertex(s, region)
                    if v == DEAD:
                        if not dead_exits:
                            out.append(VEXIT)
                    else:
                        out.append(v)
            succ[b.id] = out
        children = region.children if region is not None else [L for L in self.loops if L.parent is None]
        for C in children:
            key = ("L", id(C))
            outs = []
            for e in C.exits:
                v = self._vertex(e, region)
                if v == DEAD:
                    if not dead_exits:
                        outs.append(VEXIT)
                else:
                    outs.append(v)
            succ[key] = outs
        return succ

    def _compute_ipdom(self, succ):
        rsucc = {VEXIT: []}
        for v, outs in succ.items():
            rsucc.setdefault(v, [])
            for w in outs:
                rsucc.setdefault(w, []).append(v)
        order = []
        seen = {VEXIT}
        stack = [(VEXIT, iter(rsucc[VEXIT]))]
        while stack:
            v, it = stack[-1]
            nxt = None
            for w in it:
                if w not in seen:
                    nxt = w
                    break
            if nxt is None:
                stack.pop()
                order.append(v)
            else:
                seen.add(nxt)
                stack.append((nxt, iter(rsucc.get(nxt, ()))))
        po = {v: i for i, v in enumerate(order)}
        idom = {VEXIT: VEXIT}
        rpo = order[::-1]
        changed = True
        while changed:
            changed = False
            for v in rpo:
                if v == VEXIT:
                    continue
                new = None
                for p in succ.get(v, ()):
                    if p in idom:
                        if new is None:
                            new = p
                        else:
                            a, c = p, new
                            while a != c:
                                while po[a] < po[c]:
                                    a = idom[a]
                                while po[c] < po[a]:
                                    c = idom[c]
                            new = a
                if new is not None and idom.get(v) != new:
                    idom[v] = new
                    changed = True
        return idom

    def _ipdoms(self, region, full=False):
        key = (id(region), full)
        r = self._ipdom_cache.get(key)
        if r is None:
            r = self._compute_ipdom(self._region_graph(region, not full))
            self._ipdom_cache[key] = r
        return r

    def _ipdom_of(self, v, region):
        """Post-dominator of vertex v: first ignoring break/early-return paths
        (gives flat `if c then return end` code), else counting all exits."""
        f = self._ipdoms(region).get(v)
        if f is None or f == VEXIT:
            f = self._ipdoms(region, True).get(v)
        return f

    def _vertex_entry(self, region):
        return region.header.id if self.loop_of.get(region.header.id) is region else ("L", id(region))

    def follow_of(self, b, region):
        f = self._ipdom_of(b.id, region)
        if f is None or f == VEXIT:
            return None
        if isinstance(f, tuple):
            L = self.loop_by_key[f]
            return L.prep if L.prep is not None else L.header
        return self._bid.get(f)

    # ------------------------------------------------------------ walk
    def structure(self):
        self.collapse_conditions()
        self.find_loops()
        return self.seq(self.entry, None, None, None, None)

    def seq(self, cur, stop, region, brk, cont, first=False):
        out = []
        while cur is not None:
            if cur is stop and not first:
                break
            if cur is brk:
                if region is not None and region.flag is not None:
                    out.append(self._flag_set(region, True))
                out.append(Break())
                break
            if cur is cont and not first:
                out.append(Continue())
                break
            first = False
            Ls = self.headers.get(cur.id)
            if Ls:
                entered = None
                for L in Ls:
                    if not L.active and L.parent is region:
                        entered = L
                        break
                if entered is not None:
                    out.extend(self.loop_stmts(entered, region, brk, cont))
                    cur = entered.brk
                    continue
            if self.loop_of.get(cur.id) is not region and not (region is not None and cur.id in region.zone):
                raise DecompileError("unstructured jump into loop at pc %d" % cur.start)
            self.budget -= 1
            self.emitted[cur.id] = self.emitted.get(cur.id, 0) + 1
            if self.budget < 0:
                raise DecompileError("control flow too irregular (duplication budget exceeded)")
            out.extend(cur.stmts)
            t = cur.term
            k = t.kind
            if k == "return":
                break
            if k == "jump":
                cur = cur.succs[0]
                continue
            if k in ("fornprep", "forgprep"):
                L = self.prep_loop[cur.id]
                out.extend(self.loop_stmts(L, region, brk, cont))
                cur = L.brk
                continue
            if k == "cond":
                f = self.follow_of(cur, region) if self.loop_of.get(cur.id) is region else None
                sub_stop = f if f is not None else stop
                tb, fb = cur.succs
                then = self.seq(tb, sub_stop, region, brk, cont)
                orelse = self.seq(fb, sub_stop, region, brk, cont)
                out.append(If(t.cond, then, orelse))
                if f is None:
                    break
                cur = f
                continue
            raise DecompileError("unexpected terminator %s at pc %d" % (k, t.pc))
        return out

    def _flag_set(self, L, value):
        rd = RegDef(-1)
        rd.web = L.flag
        return Assign([rd], [Const("bool", value)])

    def loop_stmts(self, L, region, brk, cont):
        """Statements for loop L (entered from the parent region)."""
        F = self.loop_brk(L)
        L.flag = None
        pre = []
        post = []
        if L.kind != "while" and L.follow is not None and self.resolve(L.follow) is not self.resolve(F)                 and L.follow is not F:
            # breaks skip code that only runs on normal loop termination: use a flag
            if F is not None and self.resolve(L.follow) is F:
                pass
            else:
                fw = Web(-1000 - len(self.loops))
                fw.hint = "broke"
                L.flag = fw
                pre.append(self._flag_set(L, False))
                ref = RegRef(-1)
                ref.web = fw
                fw.uses.append(ref)
                fw.nuses = 1
                saved = L.zone
                L.zone = set()
                tail = self.seq(L.follow, F, region, brk, cont)
                L.zone = saved
                post.append(If(UnOp("not", ref), tail, []))
        return pre + [self.loop_stmt(L)] + post

    def loop_stmt(self, L):
        L.active = True
        brk = L.brk
        try:
            if L.kind == "fornum":
                pt = L.prep.term
                body = self.seq(L.header, L.latch, L, brk, L.latch, first=True)
                start, limit, step = pt.uses
                var = pt.defs[0].web
                lvar = L.latch.term.defs[0].web
                if lvar is not var and lvar.uses:
                    raise DecompileError("numeric for variable split")
                return NumFor(var, start, limit, step, body)
            if L.kind == "forgen":
                pt = L.prep.term
                body = self.seq(L.header, L.latch, L, brk, L.latch, first=True)
                if pt.cond is not None:
                    exprs = [pt.cond]
                else:
                    exprs = list(pt.uses)
                    while len(exprs) > 1:
                        last = deref(exprs[-1])
                        if not (type(last) is Const and last.kind == "nil"):
                            break
                        prev = deref(exprs[-2])
                        if type(prev) in (Call, MethodCall, Vararg):
                            break
                        exprs.pop()
                return GenFor([d.web for d in L.latch.term.defs], exprs, body)
            body = self.seq(L.header, None, L, brk, L.header, first=True)
            return While(Const("bool", True), body)
        finally:
            L.active = False
