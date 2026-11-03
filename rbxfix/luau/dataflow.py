"""Reaching-definition analysis: groups register definitions/uses into "webs".

Every web becomes either an inlined temporary or a named local variable.
"""
from .ast import Assign, CallStmt, Closure, Index, RegDef, Return, Upval, iter_regrefs
from .cfg import CloseUpvals, SetList, Term, DecompileError
from . import opcodes as O


class Web:
    __slots__ = ("id", "defs", "uses", "name", "is_param", "param_index", "hint",
                 "nuses", "folded", "declared", "for_owner", "self_ref_ok", "captured")

    def __init__(self, wid):
        self.id = wid
        self.defs = []   # list of (stmt, RegDef)
        self.uses = []   # list of RegRef
        self.name = None
        self.is_param = False
        self.param_index = -1
        self.hint = None
        self.nuses = 0
        self.folded = False
        self.declared = False
        self.for_owner = None
        self.captured = False

    def __repr__(self):
        return "Web(%d,%s)" % (self.id, self.name)


def stmt_defs(s):
    t = type(s)
    if t is Assign:
        return [x for x in s.targets if type(x) is RegDef]
    if t is Term:
        return s.defs
    return ()


def stmt_uses(s):
    t = type(s)
    if t is Assign:
        out = []
        for x in s.targets:
            if type(x) is Index:
                out += iter_regrefs(x.obj)
                out += iter_regrefs(x.key)
        for v in s.values:
            out += iter_regrefs(v)
        return out
    if t is CallStmt:
        return iter_regrefs(s.call)
    if t is Return:
        out = []
        for v in s.values:
            out += iter_regrefs(v)
        return out
    if t is SetList:
        out = iter_regrefs(s.table)
        for v in s.values:
            out += iter_regrefs(v)
        return out
    if t is Term:
        out = iter_regrefs(s.cond) if s.cond is not None else []
        return out + list(s.uses)
    return ()


def block_stmts(b):
    """Statements of a block including its terminator."""
    if b.term is not None and b.term.kind not in ("return", "jump"):
        return b.stmts + [b.term]
    if b.term is not None and b.term.kind == "jump":
        return b.stmts
    return b.stmts


def compute_rpo(entry):
    order = []
    seen = set()
    stack = [(entry, 0)]
    seen.add(entry.id)
    while stack:
        b, i = stack[-1]
        if i < len(b.succs):
            stack[-1] = (b, i + 1)
            s = b.succs[i]
            if s.id not in seen:
                seen.add(s.id)
                stack.append((s, 0))
        else:
            stack.pop()
            order.append(b)
    order.reverse()
    for i, b in enumerate(order):
        b.rpo = i
    return order


class _UF:
    def __init__(self):
        self.p = []

    def add(self):
        self.p.append(len(self.p))
        return len(self.p) - 1

    def find(self, x):
        p = self.p
        r = x
        while p[r] != r:
            r = p[r]
        while p[x] != r:
            p[x], x = r, p[x]
        return r

    def union(self, a, b):
        a = self.find(a)
        b = self.find(b)
        if a != b:
            if a < b:
                self.p[b] = a
            else:
                self.p[a] = b


class EntryDef:
    """Pseudo statement for parameter / undefined-on-entry definitions."""
    __slots__ = ("reg",)

    def __init__(self, reg):
        self.reg = reg


def analyze(fn, blocks):
    """Compute webs. Returns (rpo_blocks, webs list). Sets RegRef.web/RegDef.web."""
    entry = blocks[0]
    rpo = compute_rpo(entry)
    reach = set(b.id for b in rpo)
    for b in blocks:
        if b.id not in reach:
            b.rpo = -1
    for b in rpo:
        b.preds = [p for p in b.preds if p.id in reach]

    uf = _UF()
    def_info = []        # def id -> (stmt, RegDef or None, reg)
    defs_of_reg = {}     # reg -> bitmask

    def new_def(stmt, rd, reg):
        i = uf.add()
        def_info.append((stmt, rd, reg))
        defs_of_reg[reg] = defs_of_reg.get(reg, 0) | (1 << i)
        return i

    # entry definitions for parameters
    entry_defs = {}
    nparams = fn.proto.numparams
    for r in range(nparams):
        entry_defs[r] = new_def(EntryDef(r), None, r)

    # number all defs and collect per-block gen/kill
    blk_stmts = {}
    gen = {}
    for b in rpo:
        sts = block_stmts(b)
        blk_stmts[b.id] = sts
        last = {}
        for s in sts:
            for rd in stmt_defs(s):
                d = new_def(s, rd, rd.reg)
                rd.web = d  # temporarily store def id
                last[rd.reg] = d
        gen[b.id] = last

    gen_mask = {}
    kill_mask = {}
    for b in rpo:
        g = 0
        k = 0
        for reg, d in gen[b.id].items():
            g |= 1 << d
            k |= defs_of_reg[reg]
        gen_mask[b.id] = g
        kill_mask[b.id] = k

    entry_mask = 0
    for d in entry_defs.values():
        entry_mask |= 1 << d
    IN = {b.id: 0 for b in rpo}
    OUT = {b.id: 0 for b in rpo}
    changed = True
    while changed:
        changed = False
        for b in rpo:
            if b is entry:
                inn = entry_mask
                for p in b.preds:
                    inn |= OUT[p.id]
            else:
                inn = 0
                for p in b.preds:
                    inn |= OUT[p.id]
            out = gen_mask[b.id] | (inn & ~kill_mask[b.id])
            IN[b.id] = inn
            if out != OUT[b.id]:
                OUT[b.id] = out
                changed = True

    undefined_defs = {}

    def reaching_for(reg, cur_local, inmask):
        d = cur_local.get(reg)
        if d is not None:
            return (d,)
        m = inmask & defs_of_reg.get(reg, 0)
        if not m:
            return None
        res = []
        while m:
            low = m & -m
            res.append(low.bit_length() - 1)
            m ^= low
        return res

    all_uses = []
    for b in rpo:
        cur = {}
        inmask = IN[b.id]
        for s in blk_stmts[b.id]:
            selfcap = None
            if (type(s) is Assign and len(s.values) == 1 and type(s.values[0]) is Closure
                    and len(s.targets) == 1 and type(s.targets[0]) is RegDef):
                # the VM stores the new closure in its target register before
                # processing captures, so a capture of that register sees the closure
                tr = s.targets[0]
                selfcap = {id(c) for c in s.values[0].captures if type(c) is not Upval and c.reg == tr.reg}
            for u in stmt_uses(s):
                u.stmt = s
                if selfcap and id(u) in selfcap:
                    u.web = s.targets[0].web
                    all_uses.append(u)
                    continue
                ds = reaching_for(u.reg, cur, inmask)
                if not ds:
                    # read of a register never written: treat as an implicitly nil local
                    d = undefined_defs.get(u.reg)
                    if d is None:
                        d = new_def(EntryDef(u.reg), None, u.reg)
                        undefined_defs[u.reg] = d
                    ds = (d,)
                first = ds[0]
                for d in ds[1:]:
                    uf.union(first, d)
                u.web = first
                all_uses.append(u)
            for rd in stmt_defs(s):
                cur[rd.reg] = rd.web

    # ---- captured-by-reference locals: merge later redefinitions of the register
    for b in rpo:
        sts = blk_stmts[b.id]
        for si, s in enumerate(sts):
            if type(s) is not Assign or len(s.values) != 1 or type(s.values[0]) is not Closure:
                continue
            clo = s.values[0]
            ctypes = clo.fn.capture_types
            for ci, cap in enumerate(clo.captures):
                if ctypes[ci] != O.LCT_REF:
                    continue
                reg = cap.reg
                root = cap.web
                _merge_ref_defs(uf, b, si, reg, root, blk_stmts)

    # ---- build webs
    webs = {}

    def web_of(d):
        r = uf.find(d)
        w = webs.get(r)
        if w is None:
            w = Web(r)
            webs[r] = w
        return w

    for d, (stmt, rd, reg) in enumerate(def_info):
        w = web_of(d)
        if rd is not None:
            w.defs.append((stmt, rd))
            rd.web = w
        elif type(stmt) is EntryDef:
            if reg < nparams and entry_defs.get(reg) == d:
                w.is_param = True
                w.param_index = reg
            else:
                w.defs.append((stmt, None))
    for u in all_uses:
        w = web_of(u.web)
        u.web = w
        w.uses.append(u)
    # parameters always exist as webs
    fn.param_webs = [web_of(entry_defs[r]) for r in range(nparams)]
    fn.entry_undefined = [web_of(d) for d in undefined_defs.values()]
    for w in webs.values():
        w.nuses = len(w.uses)
    return rpo, list(webs.values())


def _merge_ref_defs(uf, start_block, start_index, reg, root, blk_stmts):
    seen = set()
    work = [(start_block, start_index + 1)]
    while work:
        b, i = work.pop()
        sts = blk_stmts[b.id]
        stopped = False
        while i < len(sts):
            s = sts[i]
            if type(s) is CloseUpvals and s.reg <= reg:
                stopped = True
                break
            for rd in stmt_defs(s):
                if rd.reg == reg:
                    uf.union(root, rd.web)
            i += 1
        if stopped:
            continue
        for sb in b.succs:
            if sb.rpo >= 0 and sb.id not in seen:
                seen.add(sb.id)
                work.append((sb, 0))
