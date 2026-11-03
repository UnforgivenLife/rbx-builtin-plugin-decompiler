"""Lifting of Luau instructions into basic blocks of IR statements."""
from . import opcodes as O
from .ast import (Assign, BinOp, Call, CallStmt, Closure, Concat, Const, Global, Index,
                  MethodCall, RegDef, RegRef, Return, Stmt, TableCons, UnOp, Upval, Vararg)
from .bytecode import (K_BOOL, K_CLOSURE, K_IMPORT, K_INTEGER, K_NIL, K_NUMBER, K_STRING,
                       K_TABLE, K_TABLE_CONST, K_VECTOR, K_VECTORD)

MULT = 1000  # pseudo register holding a variable number of values ("top")

NOFOLD = 1      # RegRef must never be inlined
PUREFOLD = 2    # RegRef may only be inlined if the expression is side-effect free


class DecompileError(Exception):
    pass


# ---------------------------------------------------------------- pseudo stmts
class CloseUpvals(Stmt):
    __slots__ = ("reg",)

    def __init__(self, reg):
        self.reg = reg


class SetList(Stmt):
    __slots__ = ("table", "values", "start", "pc")

    def __init__(self, table, values, start, pc):
        self.table = table
        self.values = values
        self.start = start
        self.pc = pc


class Term(Stmt):
    """Block terminator.

    kind: 'jump' | 'cond' | 'return' | 'fornprep' | 'fornloop' | 'forgprep' | 'forgloop' | 'fall'
    """
    __slots__ = ("kind", "cond", "base", "nvars", "uses", "defs", "pc", "gen_kind")

    def __init__(self, kind, pc):
        self.kind = kind
        self.cond = None
        self.base = 0
        self.nvars = 0
        self.uses = []
        self.defs = []
        self.pc = pc
        self.gen_kind = None


class Block:
    __slots__ = ("id", "start", "end", "stmts", "term", "succs", "preds", "lines", "rpo")

    def __init__(self, bid, start, end):
        self.id = bid
        self.start = start
        self.end = end
        self.stmts = []
        self.term = None
        self.succs = []   # for 'cond': [true_target, false_target]
        self.preds = []
        self.rpo = -1

    def __repr__(self):
        return "B%d[%d:%d]" % (self.id, self.start, self.end)


_JUMP_OPS = {O.JUMP, O.JUMPBACK, O.JUMPX}
_COND_OPS = {O.JUMPIF, O.JUMPIFNOT, O.JUMPIFEQ, O.JUMPIFLE, O.JUMPIFLT, O.JUMPIFNOTEQ,
             O.JUMPIFNOTLE, O.JUMPIFNOTLT, O.JUMPXEQKNIL, O.JUMPXEQKB, O.JUMPXEQKN, O.JUMPXEQKS}
_FORGPREP_OPS = {O.FORGPREP, O.FORGPREP_NEXT, O.FORGPREP_INEXT}
_SKIP_OPS = {O.NOP, O.BREAK, O.COVERAGE, O.PREPVARARGS, O.NATIVECALL, O.FASTCALL, O.FASTCALL1,
             O.FASTCALL2, O.FASTCALL2K, O.FASTCALL3}

_ARITH = {O.ADD: "+", O.SUB: "-", O.MUL: "*", O.DIV: "/", O.MOD: "%", O.POW: "^", O.IDIV: "//"}
_ARITHK = {O.ADDK: "+", O.SUBK: "-", O.MULK: "*", O.DIVK: "/", O.MODK: "%", O.POWK: "^",
           O.IDIVK: "//"}


def jump_target(ins):
    op = ins.op
    if op == O.JUMPX:
        return ins.pc + 1 + ins.e
    if op == O.LOADB:
        return ins.pc + 1 + ins.c
    return ins.pc + 1 + ins.d


class Lifter:
    def __init__(self, fn):
        self.fn = fn
        self.proto = fn.proto
        self.bc = fn.bc
        self.K = self.proto.constants

    # --------------------------------------------------------------- consts
    def kstr(self, idx):
        k = self.K[idx]
        if k.kind != K_STRING:
            raise DecompileError("constant %d is not a string" % idx)
        return k.value

    def kexpr(self, idx):
        k = self.K[idx]
        kind = k.kind
        if kind == K_NIL:
            return Const("nil")
        if kind == K_BOOL:
            return Const("bool", k.value)
        if kind == K_NUMBER:
            return Const("number", k.value)
        if kind == K_STRING:
            return Const("string", k.value)
        if kind == K_VECTOR or kind == K_VECTORD:
            return Const("vector", k.value)
        if kind == K_INTEGER:
            return Const("integer", k.value)
        if kind == K_IMPORT:
            return self.import_expr(k.value)
        raise DecompileError("unsupported constant kind %d in expression" % kind)

    def import_expr(self, iid):
        count = iid >> 30
        ids = [(iid >> 20) & 1023, (iid >> 10) & 1023, iid & 1023][:count]
        if not ids:
            raise DecompileError("bad import")
        e = Global(self.kstr(ids[0]).decode("utf-8", "replace"), True)
        for i in ids[1:]:
            e = Index(e, Const("string", self.kstr(i)))
        return e

    def table_template(self, idx):
        k = self.K[idx]
        items = []
        if k.kind == K_TABLE_CONST or k.kind == K_TABLE:
            for key, cidx in k.value:
                kx = self.kexpr(key)
                if cidx >= 0:
                    items.append((kx, self.kexpr(cidx)))
        else:
            raise DecompileError("DUPTABLE with non-table constant")
        return TableCons(items)

    # ----------------------------------------------------------------- run
    def run(self):
        p = self.proto
        insns = p.insns
        if not insns:
            raise DecompileError("empty function")
        at = p.insn_at
        leaders = {0}
        for ins in insns:
            op = ins.op
            nxt = ins.pc + ins.size
            if op in _JUMP_OPS or op in _COND_OPS or (op == O.LOADB and ins.c):
                leaders.add(jump_target(ins))
                leaders.add(nxt)
            elif op == O.FORNPREP or op in _FORGPREP_OPS:
                leaders.add(jump_target(ins))
                leaders.add(nxt)
            elif op == O.FORNLOOP or op == O.FORGLOOP:
                leaders.add(ins.pc)
                leaders.add(jump_target(ins))
                leaders.add(nxt)
            elif op == O.RETURN:
                leaders.add(nxt)
        end_pc = insns[-1].pc + insns[-1].size
        for l in leaders:
            if l != end_pc and l not in at:
                raise DecompileError("jump into the middle of an instruction (pc %d)" % l)
        leaders = sorted(l for l in leaders if l < end_pc)
        blocks = []
        by_start = {}
        for i, s in enumerate(leaders):
            e = leaders[i + 1] if i + 1 < len(leaders) else end_pc
            b = Block(i, s, e)
            blocks.append(b)
            by_start[s] = b
        self.by_start = by_start
        for b in blocks:
            self.lift_block(b)
        # The bytecode peephole optimizer may copy a short `return` block so that
        # FORNPREP's "no iterations" edge targets a twin of the loop's natural
        # exit.  Identical code on identical state behaves identically, so point
        # the edge at the natural exit (keeps the loop single-exit).
        words = p.code_words
        for b in blocks:
            t = b.term
            if t is not None and t.kind == "fornprep":
                skip = b.succs[1]
                loop_ins = None
                for bb in blocks:
                    if bb.term is not None and bb.term.kind == "fornloop" and bb.succs[0] is b.succs[0]:
                        loop_ins = bb
                if loop_ins is None:
                    continue
                nat = by_start.get(loop_ins.end)
                if nat is not None and nat is not skip and nat.term.kind == "return" \
                        and skip.term.kind == "return" \
                        and words[nat.start:nat.end] == words[skip.start:skip.end]:
                    b.succs[1] = nat
        # wire edges
        for b in blocks:
            for s in b.succs:
                s.preds.append(b)
        return blocks

    def blk(self, pc):
        b = self.by_start.get(pc)
        if b is None:
            raise DecompileError("jump to pc %d outside function" % pc)
        return b

    def lift_block(self, b):
        p = self.proto
        at = p.insn_at
        stmts = b.stmts
        pc = b.start
        mult_base = None
        R = RegRef
        fn = self.fn
        while pc < b.end:
            ins = at[pc]
            op = ins.op
            A = ins.a
            nxt = pc + ins.size
            if op in _SKIP_OPS:
                pass
            elif op == O.LOADNIL:
                stmts.append(Assign([RegDef(A)], [Const("nil")], pc))
            elif op == O.LOADB:
                stmts.append(Assign([RegDef(A)], [Const("bool", bool(ins.b))], pc))
                if ins.c:
                    t = Term("jump", pc)
                    b.term = t
                    b.succs = [self.blk(jump_target(ins))]
                    if nxt != b.end:
                        raise DecompileError("LOADB jump not at block end")
                    return
            elif op == O.LOADN:
                stmts.append(Assign([RegDef(A)], [Const("number", float(ins.d))], pc))
            elif op == O.LOADK:
                stmts.append(Assign([RegDef(A)], [self.kexpr(ins.d)], pc))
            elif op == O.LOADKX:
                stmts.append(Assign([RegDef(A)], [self.kexpr(ins.aux)], pc))
            elif op == O.MOVE:
                stmts.append(Assign([RegDef(A)], [R(ins.b)], pc))
            elif op == O.GETGLOBAL:
                stmts.append(Assign([RegDef(A)], [Global(self.kstr(ins.aux).decode("utf-8", "replace"))], pc))
            elif op == O.SETGLOBAL:
                stmts.append(Assign([Global(self.kstr(ins.aux).decode("utf-8", "replace"))], [R(A)], pc))
            elif op == O.GETUPVAL:
                stmts.append(Assign([RegDef(A)], [Upval(ins.b, fn)], pc))
            elif op == O.SETUPVAL:
                stmts.append(Assign([Upval(ins.b, fn)], [R(A)], pc))
            elif op == O.CLOSEUPVALS:
                stmts.append(CloseUpvals(A))
            elif op == O.GETIMPORT:
                stmts.append(Assign([RegDef(A)], [self.import_expr(ins.aux)], pc))
            elif op == O.GETTABLE:
                stmts.append(Assign([RegDef(A)], [Index(R(ins.b), R(ins.c))], pc))
            elif op == O.SETTABLE:
                stmts.append(Assign([Index(R(ins.b), R(ins.c))], [R(A)], pc))
            elif op == O.GETTABLEKS or op == O.GETUDATAKS:
                kidx = ins.aux if op == O.GETTABLEKS else ins.aux & 0xFFFF
                stmts.append(Assign([RegDef(A)], [Index(R(ins.b), Const("string", self.kstr(kidx)))], pc))
            elif op == O.SETTABLEKS or op == O.SETUDATAKS:
                kidx = ins.aux if op == O.SETTABLEKS else ins.aux & 0xFFFF
                stmts.append(Assign([Index(R(ins.b), Const("string", self.kstr(kidx)))], [R(A)], pc))
            elif op == O.GETTABLEN:
                stmts.append(Assign([RegDef(A)], [Index(R(ins.b), Const("number", float(ins.c + 1)))], pc))
            elif op == O.SETTABLEN:
                stmts.append(Assign([Index(R(ins.b), Const("number", float(ins.c + 1)))], [R(A)], pc))
            elif op == O.NEWCLOSURE or op == O.DUPCLOSURE:
                if op == O.NEWCLOSURE:
                    pid = p.children[ins.d]
                else:
                    k = self.K[ins.d]
                    if k.kind != K_CLOSURE:
                        raise DecompileError("DUPCLOSURE of non-closure constant")
                    pid = k.value
                child = fn.child(pid)
                caps = []
                ctypes = []
                cpc = nxt
                for _ in range(child.proto.nups):
                    ci = at.get(cpc)
                    if ci is None or ci.op != O.CAPTURE:
                        raise DecompileError("missing CAPTURE after closure")
                    if ci.a == O.LCT_UPVAL:
                        caps.append(Upval(ci.b, fn))
                    else:
                        caps.append(R(ci.b, NOFOLD))
                    ctypes.append(ci.a)
                    cpc += 1
                if cpc > b.end:
                    raise DecompileError("CAPTURE crosses block boundary")
                clo = Closure(child, caps)
                child.capture_types = ctypes
                stmts.append(Assign([RegDef(A)], [clo], pc))
                nxt = cpc
            elif op == O.CAPTURE:
                raise DecompileError("stray CAPTURE")
            elif op == O.NAMECALL or op == O.NAMECALLUDATA:
                ci = at.get(nxt)
                if ci is None or ci.op != O.CALL or ci.a != A:
                    raise DecompileError("NAMECALL not followed by CALL")
                kidx = ins.aux if op == O.NAMECALL else ins.aux & 0xFFFF
                name = self.kstr(kidx)
                args, mult_base = self.call_args(ci, A + 2, mult_base)
                call = MethodCall(R(ins.b), name, args, ci.c - 1)
                mult_base = self.call_result(stmts, call, ci, mult_base, pc)
                nxt = ci.pc + ci.size
            elif op == O.CALL:
                args, mult_base = self.call_args(ins, A + 1, mult_base)
                call = Call(R(A), args, ins.c - 1)
                mult_base = self.call_result(stmts, call, ins, mult_base, pc)
            elif op == O.RETURN:
                if ins.b == 0:
                    if mult_base is None:
                        raise DecompileError("multret RETURN without producer")
                    vals = [R(r) for r in range(A, mult_base)] + [R(MULT)]
                    mult_base = None
                else:
                    vals = [R(r) for r in range(A, A + ins.b - 1)]
                stmts.append(Return(vals, pc))
                t = Term("return", pc)
                b.term = t
                b.succs = []
                if nxt != b.end:
                    raise DecompileError("RETURN not at block end")
                return
            elif op in _JUMP_OPS:
                b.term = Term("jump", pc)
                b.succs = [self.blk(jump_target(ins))]
                return
            elif op in _COND_OPS:
                t = Term("cond", pc)
                t.cond = self.cond_expr(ins)
                b.term = t
                b.succs = [self.blk(jump_target(ins)), self.blk(nxt)]
                return
            elif op in _ARITH:
                stmts.append(Assign([RegDef(A)], [BinOp(_ARITH[op], R(ins.b), R(ins.c))], pc))
            elif op in _ARITHK:
                stmts.append(Assign([RegDef(A)], [BinOp(_ARITHK[op], R(ins.b), self.kexpr(ins.c))], pc))
            elif op == O.SUBRK or op == O.DIVRK:
                o = "-" if op == O.SUBRK else "/"
                stmts.append(Assign([RegDef(A)], [BinOp(o, self.kexpr(ins.b), R(ins.c))], pc))
            elif op == O.AND or op == O.OR:
                stmts.append(Assign([RegDef(A)], [BinOp("and" if op == O.AND else "or", R(ins.b), R(ins.c, PUREFOLD))], pc))
            elif op == O.ANDK or op == O.ORK:
                stmts.append(Assign([RegDef(A)], [BinOp("and" if op == O.ANDK else "or", R(ins.b), self.kexpr(ins.c))], pc))
            elif op == O.CONCAT:
                stmts.append(Assign([RegDef(A)], [Concat([R(r) for r in range(ins.b, ins.c + 1)])], pc))
            elif op == O.NOT:
                stmts.append(Assign([RegDef(A)], [UnOp("not", R(ins.b))], pc))
            elif op == O.MINUS:
                stmts.append(Assign([RegDef(A)], [UnOp("-", R(ins.b))], pc))
            elif op == O.LENGTH:
                stmts.append(Assign([RegDef(A)], [UnOp("#", R(ins.b))], pc))
            elif op == O.NEWTABLE:
                stmts.append(Assign([RegDef(A)], [TableCons([])], pc))
            elif op == O.DUPTABLE:
                stmts.append(Assign([RegDef(A)], [self.table_template(ins.d)], pc))
            elif op == O.SETLIST:
                if ins.c == 0:
                    if mult_base is None:
                        raise DecompileError("multret SETLIST without producer")
                    vals = [R(r) for r in range(ins.b, mult_base)] + [R(MULT)]
                    mult_base = None
                else:
                    vals = [R(r) for r in range(ins.b, ins.b + ins.c - 1)]
                stmts.append(SetList(R(A), vals, ins.aux, pc))
            elif op == O.GETVARARGS:
                if ins.b == 0:
                    stmts.append(Assign([RegDef(MULT)], [Vararg(-1)], pc))
                    mult_base = A
                else:
                    stmts.append(Assign([RegDef(A + i) for i in range(ins.b - 1)], [Vararg(ins.b - 1)], pc))
            elif op == O.FORNPREP:
                t = Term("fornprep", pc)
                t.base = A
                t.uses = [R(A + 2), R(A), R(A + 1)]
                t.defs = [RegDef(A + 2)]
                b.term = t
                b.succs = [self.blk(nxt), self.blk(jump_target(ins))]  # body, exit
                return
            elif op == O.FORNLOOP:
                t = Term("fornloop", pc)
                t.base = A
                t.defs = [RegDef(A + 2)]
                b.term = t
                b.succs = [self.blk(jump_target(ins)), self.blk(nxt)]  # body, exit
                return
            elif op in _FORGPREP_OPS:
                t = Term("forgprep", pc)
                t.base = A
                t.gen_kind = op
                t.uses = [R(A), R(A + 1), R(A + 2)]
                b.term = t
                b.succs = [self.blk(jump_target(ins))]  # latch (FORGLOOP)
                return
            elif op == O.FORGLOOP:
                t = Term("forgloop", pc)
                t.base = A
                t.nvars = ins.aux & 0xFF
                t.defs = [RegDef(A + 3 + i) for i in range(t.nvars)]
                b.term = t
                b.succs = [self.blk(jump_target(ins)), self.blk(nxt)]  # body, exit
                return
            else:
                raise DecompileError("unsupported opcode %s" % ins.name)
            pc = nxt
        # fell through to next leader
        b.term = Term("jump", b.end)
        nb = self.by_start.get(b.end)
        if nb is None:
            raise DecompileError("control falls off the end of the function")
        b.succs = [nb]

    def call_args(self, ins, first, mult_base):
        A = ins.a
        if ins.b == 0:
            if mult_base is None:
                raise DecompileError("multret CALL without producer")
            args = [RegRef(r) for r in range(first, mult_base)] + [RegRef(MULT)]
            return args, None
        return [RegRef(r) for r in range(first, A + ins.b)], mult_base

    def call_result(self, stmts, call, ins, mult_base, pc):
        A = ins.a
        c = ins.c
        if c == 1:
            stmts.append(CallStmt(call, pc))
        elif c == 0:
            stmts.append(Assign([RegDef(MULT)], [call], pc))
            return A
        else:
            stmts.append(Assign([RegDef(A + i) for i in range(c - 1)], [call], pc))
        return mult_base

    def cond_expr(self, ins):
        op = ins.op
        A = ins.a
        R = RegRef
        if op == O.JUMPIF:
            return R(A)
        if op == O.JUMPIFNOT:
            return UnOp("not", R(A))
        if op == O.JUMPIFEQ:
            return BinOp("==", R(A), R(ins.aux))
        if op == O.JUMPIFNOTEQ:
            return BinOp("~=", R(A), R(ins.aux))
        if op == O.JUMPIFLE:
            return BinOp("<=", R(A), R(ins.aux))
        if op == O.JUMPIFLT:
            return BinOp("<", R(A), R(ins.aux))
        if op == O.JUMPIFNOTLE:
            return UnOp("not", BinOp("<=", R(A), R(ins.aux)))
        if op == O.JUMPIFNOTLT:
            return UnOp("not", BinOp("<", R(A), R(ins.aux)))
        neg = ins.aux >> 31
        if op == O.JUMPXEQKNIL:
            k = Const("nil")
        elif op == O.JUMPXEQKB:
            k = Const("bool", bool(ins.aux & 1))
        else:
            k = self.kexpr(ins.aux & 0xFFFFFF)
        return BinOp("~=" if neg else "==", R(A), k)
