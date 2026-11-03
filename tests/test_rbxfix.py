"""Regression tests.

Run with:  python -m pytest tests      (or: python tests/test_rbxfix.py)

The tests build tiny bytecode blobs and model files in memory, so they need
no external files and run anywhere.
"""
import os
import struct
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
sys.setrecursionlimit(50000)

from rbxfix.rbxbinary import Chunk, RbxFile  # noqa: E402
from rbxfix.fixer import fix_file, instance_tree  # noqa: E402
from rbxfix.luau.bytecode import is_bytecode, parse  # noqa: E402
from rbxfix.luau.checker import check_source  # noqa: E402
from rbxfix.luau.decompiler import decompile  # noqa: E402
from rbxfix.luau.opcodes import OP  # noqa: E402


# ------------------------------------------------------------- builders
def _varint(n):
    out = bytearray()
    while True:
        b = n & 127
        n >>= 7
        out.append(b | (128 if n else 0))
        if not n:
            return bytes(out)


def _abc(op, a=0, b=0, c=0):
    return OP[op] | (a << 8) | (b << 16) | (c << 24)


def _ad(op, a, d):
    return OP[op] | (a << 8) | ((d & 0xFFFF) << 16)


def build_bytecode(strings, code, consts, maxstack=4, version=6):
    """Single vararg main function.  consts: list of ('str', i) / ('import', id)."""
    out = bytearray([version, 3])
    out += _varint(len(strings))
    for s in strings:
        out += _varint(len(s)) + s
    out += b"\0"                                  # no userdata type names
    out += _varint(1)                             # one proto
    out += bytes([maxstack, 0, 0, 1, 0])          # stack, params, upvalues, vararg, flags
    out += _varint(0)                             # no type info
    out += _varint(len(code)) + struct.pack("<%dI" % len(code), *code)
    out += _varint(len(consts))
    for kind, v in consts:
        if kind == "str":
            out += b"\3" + _varint(v)
        else:
            out += b"\4" + struct.pack("<I", v)
    out += _varint(0) + _varint(0) + _varint(0)   # children, linedefined, debugname
    out += b"\0\0"                                # no line info, no debug info
    out += _varint(0)                             # main proto index
    return bytes(out)


def hello_bytecode():
    """print("hi")"""
    imp = (1 << 30) | (0 << 20)                   # import path: K0
    code = [
        _abc("PREPVARARGS"),
        _ad("GETIMPORT", 0, 1), imp,
        _ad("LOADK", 1, 2),
        _abc("CALL", 0, 2, 1),
        _abc("RETURN", 0, 1),
    ]
    return build_bytecode([b"print", b"hi"], code, [("str", 1), ("import", imp), ("str", 2)])


def _referents(refs):
    vals, prev = [], 0
    for r in refs:
        d = r - prev
        prev = r
        vals.append(((d << 1) ^ (d >> 31)) & 0xFFFFFFFF)
    n = len(vals)
    planes = bytearray(4 * n)
    for i, v in enumerate(vals):
        for p in range(4):
            planes[p * n + i] = (v >> (24 - 8 * p)) & 0xFF
    return bytes(planes)


def _string(b):
    return struct.pack("<I", len(b)) + b


def build_signed_model(source_blob, name=b"MyModule"):
    """A one-ModuleScript model shaped like Studio's signed plugin files."""
    rf = RbxFile()
    rf.num_classes, rf.num_instances = 1, 1
    inst = struct.pack("<I", 0) + _string(b"ModuleScript") + b"\0" + struct.pack("<I", 1) + _referents([0])
    prop_name = struct.pack("<I", 0) + _string(b"Name") + b"\x01" + _string(name)
    prop_src = struct.pack("<I", 0) + _string(b"Source") + b"\x1d" + _string(source_blob)
    prnt = b"\0" + struct.pack("<I", 1) + _referents([0]) + _referents([-1])
    rf.chunks = [Chunk("INST", inst), Chunk("PROP", prop_name), Chunk("PROP", prop_src),
                 Chunk("PRNT", prnt), Chunk("SIGN", b"\0" * 16), Chunk("END", b"</roblox>")]
    return rf


# ------------------------------------------------------------------ tests
def test_bytecode_parser():
    bc = parse(hello_bytecode())
    assert bc.version == 6 and len(bc.protos) == 1
    assert [i.name for i in bc.protos[0].insns] == ["PREPVARARGS", "GETIMPORT", "LOADK", "CALL", "RETURN"]
    assert is_bytecode(hello_bytecode())
    assert not is_bytecode(b"\tprint('plain source')")


def test_decompile_synthetic():
    src, st = decompile(hello_bytecode(), header=False)
    assert src.strip() == 'print("hi")', src
    assert st["failed"] == 0
    assert check_source(src, st["globals"]) == []


def test_fix_synthetic_model():
    d = tempfile.mkdtemp()
    inp = os.path.join(d, "in.rbxm")
    out = os.path.join(d, "out", "in.rbxm")
    model = build_signed_model(hello_bytecode())
    model.save(inp)
    rep = fix_file(inp, out, check=True)
    assert rep.scripts == 1 and rep.failed_functions == 0 and rep.problems == 0
    assert rep.removed_chunks == ["SIGN"]
    fixed = RbxFile.load(out)
    assert "SIGN" not in [c.name for c in fixed.chunks]
    tree = instance_tree(fixed)[0]
    assert tree == {0: {"class": "ModuleScript", "name": "MyModule", "parent": -1}}
    srcs = [(pc.type, pc.values()) for pc in fixed.string_props() if pc.name == "Source"]
    assert srcs[0][0] == 0x01 and b'print("hi")' in srcs[0][1][0]


def test_writer_round_trip_synthetic():
    model = build_signed_model(hello_bytecode())
    again = RbxFile.from_bytes(model.to_bytes())
    assert [(c.name, c.data) for c in again.chunks] == [(c.name, c.data) for c in model.chunks]
    again = RbxFile.from_bytes(model.to_bytes(compress=False))
    assert [(c.name, c.data) for c in again.chunks] == [(c.name, c.data) for c in model.chunks]


def test_checker_detects_problems():
    assert check_source("local a = 1\nprint(b)", {"print"})
    assert check_source("if x then", {"x"})
    assert check_source("local g = function() return g end", set())
    assert not check_source("local function f() return f end", set())
    assert not check_source("local a = `x{1 + 2}y`", set())
    assert not check_source("repeat local z = 1 until z", set())


if __name__ == "__main__":
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
            print("ok", name)
