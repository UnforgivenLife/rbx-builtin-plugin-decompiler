"""Deserializer for Luau bytecode blobs (versions 3..14).

Mirrors the layout read by Luau's VM/src/lvmload.cpp.
"""
import struct

from .opcodes import OP_HAS_AUX, OPNAMES

# constant kinds
K_NIL, K_BOOL, K_NUMBER, K_STRING, K_IMPORT, K_TABLE, K_CLOSURE, K_VECTOR, \
    K_TABLE_CONST, K_INTEGER, K_CLASS_SHAPE, K_VECTORD = range(12)


class BytecodeError(Exception):
    pass


class Constant:
    __slots__ = ("kind", "value")

    def __init__(self, kind, value):
        self.kind = kind
        self.value = value

    def __repr__(self):
        return "K(%d,%r)" % (self.kind, self.value)


class Instruction:
    __slots__ = ("pc", "op", "a", "b", "c", "d", "e", "aux", "word")

    def __init__(self, pc, word, aux):
        self.pc = pc
        self.word = word
        self.op = word & 0xFF
        self.a = (word >> 8) & 0xFF
        self.b = (word >> 16) & 0xFF
        self.c = (word >> 24) & 0xFF
        d = word >> 16
        self.d = d - 0x10000 if d & 0x8000 else d
        e = word >> 8
        self.e = e - 0x1000000 if e & 0x800000 else e
        self.aux = aux

    @property
    def name(self):
        return OPNAMES[self.op] if self.op < len(OPNAMES) else "OP%d" % self.op

    @property
    def size(self):
        return 2 if self.aux is not None else 1

    def __repr__(self):
        return "%d: %s A=%d B=%d C=%d D=%d aux=%r" % (
            self.pc, self.name, self.a, self.b, self.c, self.d, self.aux)


class Proto:
    def __init__(self):
        self.index = 0
        self.maxstacksize = 0
        self.numparams = 0
        self.nups = 0
        self.is_vararg = False
        self.flags = 0
        self.typeinfo = b""
        self.code_words = []
        self.insns = []          # decoded instructions (one per real instruction)
        self.insn_at = {}        # pc -> Instruction
        self.constants = []
        self.children = []       # list of proto indices
        self.linedefined = 0
        self.debugname = None
        self.lineinfo = None     # list of line per pc or None
        self.locvars = []        # (name, startpc, endpc, reg)
        self.upvalnames = []

    def decode(self):
        words = self.code_words
        pc = 0
        n = len(words)
        insns = []
        while pc < n:
            w = words[pc]
            op = w & 0xFF
            has_aux = op < len(OP_HAS_AUX) and OP_HAS_AUX[op]
            aux = words[pc + 1] if has_aux and pc + 1 < n else None
            ins = Instruction(pc, w, aux)
            insns.append(ins)
            self.insn_at[pc] = ins
            pc += 2 if has_aux else 1
        self.insns = insns


class Bytecode:
    def __init__(self):
        self.version = 0
        self.types_version = 0
        self.strings = []
        self.userdata_types = {}
        self.protos = []
        self.main = 0

    @property
    def main_proto(self):
        return self.protos[self.main]


class _Reader:
    __slots__ = ("d", "p")

    def __init__(self, data):
        self.d = data
        self.p = 0

    def u8(self):
        v = self.d[self.p]
        self.p += 1
        return v

    def varint(self):
        r = 0
        sh = 0
        d = self.d
        while True:
            b = d[self.p]
            self.p += 1
            r |= (b & 127) << sh
            sh += 7
            if not b & 128:
                return r

    def raw(self, n):
        if self.p + n > len(self.d):
            raise BytecodeError("unexpected end of bytecode")
        v = self.d[self.p:self.p + n]
        self.p += n
        return v

    def unpack(self, fmt, size):
        v = struct.unpack_from(fmt, self.d, self.p)
        self.p += size
        return v


def is_bytecode(data):
    """Heuristic: does this blob look like Luau bytecode rather than source text?"""
    if not data:
        return False
    v = data[0]
    if v == 0:
        return True  # compile-error blob
    if not (3 <= v <= 14 or v == 100):
        return False
    try:
        parse(data)
        return True
    except Exception:
        return False


def parse(data):
    if isinstance(data, str):
        data = data.encode("latin-1")
    r = _Reader(data)
    bc = Bytecode()
    try:
        bc.version = r.u8()
        if bc.version == 0:
            raise BytecodeError("bytecode contains a compile error: " + data[1:].decode("utf-8", "replace"))
        if bc.version >= 4:
            bc.types_version = r.u8()

        strings = [r.raw(r.varint()) for _ in range(r.varint())]
        bc.strings = strings

        def rstr():
            i = r.varint()
            return None if i == 0 else strings[i - 1]

        if bc.types_version == 3:
            while True:
                idx = r.u8()
                if idx == 0:
                    break
                bc.userdata_types[idx] = rstr()

        nprotos = r.varint()
        for pi in range(nprotos):
            p = Proto()
            p.index = pi
            if bc.version >= 12:
                r.varint()  # proto size
            p.maxstacksize, p.numparams, p.nups, isva = r.unpack("<BBBB", 4)
            p.is_vararg = bool(isva)
            if bc.version >= 4:
                p.flags = r.u8()
                p.typeinfo = r.raw(r.varint())
            ncode = r.varint()
            p.code_words = list(struct.unpack_from("<%dI" % ncode, r.raw(4 * ncode)))
            nk = r.varint()
            ks = []
            for _ in range(nk):
                t = r.u8()
                if t == K_NIL:
                    ks.append(Constant(t, None))
                elif t == K_BOOL:
                    ks.append(Constant(t, bool(r.u8())))
                elif t == K_NUMBER:
                    ks.append(Constant(t, r.unpack("<d", 8)[0]))
                elif t == K_STRING:
                    ks.append(Constant(t, rstr()))
                elif t == K_IMPORT:
                    ks.append(Constant(t, r.unpack("<I", 4)[0]))
                elif t == K_TABLE:
                    ks.append(Constant(t, [(r.varint(), -1) for _ in range(r.varint())]))
                elif t == K_TABLE_CONST:
                    items = []
                    for _ in range(r.varint()):
                        key = r.varint()
                        items.append((key, r.unpack("<i", 4)[0]))
                    ks.append(Constant(t, items))
                elif t == K_CLOSURE:
                    ks.append(Constant(t, r.varint()))
                elif t == K_VECTOR:
                    ks.append(Constant(t, r.unpack("<4f", 16)))
                elif t == K_VECTORD:
                    ks.append(Constant(t, r.unpack("<4d", 32)))
                elif t == K_INTEGER:
                    neg = r.u8()
                    mag = 0
                    sh = 0
                    while True:
                        b = r.u8()
                        mag |= (b & 127) << sh
                        sh += 7
                        if not b & 128:
                            break
                    ks.append(Constant(t, -mag if neg else mag))
                elif t == K_CLASS_SHAPE:
                    raise BytecodeError("Luau class constants are not supported")
                else:
                    raise BytecodeError("unknown constant kind %d" % t)
            p.constants = ks
            p.children = [r.varint() for _ in range(r.varint())]
            p.linedefined = r.varint()
            dn = rstr()
            p.debugname = dn.decode("utf-8", "replace") if dn is not None else None
            if r.u8():
                gap = r.u8()
                offs = r.raw(ncode)
                intervals = ((ncode - 1) >> gap) + 1
                abs_ = struct.unpack_from("<%di" % intervals, r.raw(4 * intervals))
                lines = []
                last = 0
                for j in range(ncode):
                    last = (last + offs[j]) & 0xFF
                    lines.append(last)
                acc = 0
                absl = []
                for v in abs_:
                    acc += v
                    absl.append(acc)
                p.lineinfo = [absl[j >> gap] + lines[j] for j in range(ncode)]
            if r.u8():
                for _ in range(r.varint()):
                    name = rstr()
                    sp = r.varint()
                    ep = r.varint()
                    reg = r.u8()
                    p.locvars.append((name, sp, ep, reg))
                for _ in range(r.varint()):
                    p.upvalnames.append(rstr())
            if bc.version >= 11:
                for _ in range(r.varint()):
                    st = r.u8()
                    r.varint()
                    if st not in (0, 1):
                        raise BytecodeError("unknown feedback slot type")
            if bc.version >= 12 and (p.flags & (1 << 3)):
                r.varint()
            p.decode()
            bc.protos.append(p)
        bc.main = r.varint()
    except IndexError:
        raise BytecodeError("truncated bytecode")
    except struct.error:
        raise BytecodeError("truncated bytecode")
    if r.p != len(data):
        raise BytecodeError("trailing data after bytecode (%d of %d bytes used)" % (r.p, len(data)))
    return bc
