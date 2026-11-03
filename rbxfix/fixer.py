"""Convert Studio-internal (signed, bytecode-only) model files into regular ones.

What makes Studio reject these files ("The file is corrupted"):
  * a SIGN chunk (and usually a HASH chunk) - Roblox's signature over the
    built-in plugin, only accepted when Studio loads its own plugins
  * script `Source` stored as property type 0x1D (ProtectedString) holding
    compiled Luau *bytecode* instead of source text

The fix: decompile every bytecode Source back to Luau, store all
ProtectedString properties as ordinary strings (type 0x01, which is what
Studio itself writes) and drop the SIGN/HASH chunks.
"""
import os
import struct
import sys
import threading

from .rbxbinary import PT_PROTECTED_STRING, PT_STRING, PropChunk, RbxFile
from .luau.bytecode import BytecodeError, is_bytecode, parse as parse_bytecode
from .luau.decompiler import decompile, disassemble
from .luau.emit import fmt_string

SIGNATURE_CHUNKS = ("SIGN", "HASH")
STACK_SIZE = 256 * 1024 * 1024 - 4096


# ------------------------------------------------------------ decompilation
def decompile_source(blob, check=False):
    """Bytecode blob -> (source_text, info dict). Never raises."""
    info = {"functions": 0, "failed": 0, "errors": [], "problems": []}
    try:
        src, st = decompile(blob)
        info["functions"] = st["functions"]
        info["failed"] = st["failed"]
        info["errors"] = st["errors"]
        if check:
            from .luau.checker import check_source
            info["problems"] = check_source(src, st["globals"])
        return src, info
    except Exception as e:  # whole-script failure: keep a loadable stub
        info["failed"] = 1
        info["errors"] = [("main chunk", "%s: %s" % (type(e).__name__, e))]
        lines = ["-- rbxfix: this script could not be decompiled (%s)" % e,
                 "-- Disassembly of the original bytecode follows for reference.", "--[==["]
        try:
            lines.append(disassemble(blob).replace("]==]", "] ==]"))
        except Exception:
            lines.append("(disassembly unavailable)")
        lines.append("]==]")
        lines.append("error(%s)" % fmt_string("rbxfix: script could not be decompiled"))
        return "\n".join(lines) + "\n", info


def _run_with_big_stack(fn, *args):
    """The decompiler is recursive; give it a large stack for deep code."""
    result = {}

    def target():
        try:
            result["value"] = fn(*args)
        except BaseException as e:  # pragma: no cover
            result["error"] = e

    old = threading.stack_size()
    try:
        # not every platform accepts every size (e.g. 32-bit builds): fall back
        for size in (STACK_SIZE, 64 * 1024 * 1024, 16 * 1024 * 1024, 0):
            try:
                threading.stack_size(size)
                break
            except (ValueError, RuntimeError):
                continue
        t = threading.Thread(target=target)
        t.start()
        t.join()
    finally:
        threading.stack_size(old)
    if "error" in result:
        raise result["error"]
    return result["value"]


def _decompile_many(blobs, check):
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 50000))
    return [decompile_source(b, check) for b in blobs]


def decompile_batch(blobs, check=False):
    return _run_with_big_stack(_decompile_many, blobs, check)


# ------------------------------------------------------------- instances
def _read_referents(data, off, count):
    """Interleaved, zig-zag, delta-encoded int32 array."""
    n = count
    b = data[off:off + 4 * n]
    out = []
    acc = 0
    for i in range(n):
        v = (b[i] << 24) | (b[n + i] << 16) | (b[2 * n + i] << 8) | b[3 * n + i]
        v = (v >> 1) ^ -(v & 1)
        acc += v
        out.append(acc)
    return out, off + 4 * n


def instance_tree(rf):
    """referent -> {class, name, parent}; plus class id -> referent list."""
    inst = {}
    class_refs = {}
    for ch in rf.chunks:
        if ch.name == "INST":
            d = ch.data
            cid, n = struct.unpack_from("<II", d, 0)
            cname = d[8:8 + n].decode("utf-8", "replace")
            off = 8 + n
            off += 1  # object format
            count, = struct.unpack_from("<I", d, off)
            off += 4
            refs, off = _read_referents(d, off, count)
            class_refs[cid] = refs
            for r in refs:
                inst[r] = {"class": cname, "name": cname, "parent": -1}
    for pc in rf.string_props():
        if pc.name == "Name":
            for r, v in zip(class_refs.get(pc.class_id, ()), pc.values()):
                inst[r]["name"] = v.decode("utf-8", "replace")
    for ch in rf.chunks:
        if ch.name == "PRNT":
            d = ch.data
            count, = struct.unpack_from("<I", d, 1)
            kids, off = _read_referents(d, 5, count)
            parents, _ = _read_referents(d, off, count)
            for k, p in zip(kids, parents):
                if k in inst:
                    inst[k]["parent"] = p
    return inst, class_refs


def instance_path(inst, ref):
    parts = []
    seen = set()
    while ref in inst and ref not in seen:
        seen.add(ref)
        parts.append(inst[ref]["name"])
        ref = inst[ref]["parent"]
    return list(reversed(parts))


# ----------------------------------------------------------------- fixing
class FileReport:
    def __init__(self, path):
        self.path = path
        self.scripts = 0
        self.text_sources = 0
        self.functions = 0
        self.failed_functions = 0
        self.failed_scripts = 0
        self.problems = 0
        self.removed_chunks = []
        self.converted_props = 0
        self.errors = []      # (script path, function, message)

    def summary(self):
        s = "%s: %d bytecode scripts decompiled" % (os.path.basename(self.path), self.scripts)
        if self.text_sources:
            s += ", %d already plain text" % self.text_sources
        if self.functions:
            ok = self.functions - self.failed_functions
            s += ", %d/%d functions (%.2f%%)" % (ok, self.functions, 100.0 * ok / self.functions)
        if self.removed_chunks:
            s += ", removed %s" % "/".join(sorted(set(self.removed_chunks)))
        if self.problems:
            s += ", %d checker warnings" % self.problems
        return s


def collect_jobs(rf):
    """List of (PropChunk, value index, blob) for every bytecode script source."""
    jobs = []
    for pc in rf.string_props():
        if pc.type != PT_PROTECTED_STRING and pc.name != "Source":
            continue
        for i, v in enumerate(pc.values()):
            if is_bytecode(v):
                jobs.append((pc, i, v))
    return jobs


def fix_file(path, out_path, decompile_fn=None, check=False, extract_dir=None, keep_signature=False):
    """Fix one file. `decompile_fn(list_of_blobs) -> list of (src, info)` allows
    the caller to parallelise; defaults to in-process decompilation."""
    rf = RbxFile.load(path)
    rep = FileReport(path)
    jobs = collect_jobs(rf)
    blobs = [j[2] for j in jobs]
    if decompile_fn is None:
        results = decompile_batch(blobs, check)
    else:
        results = decompile_fn(blobs)

    # paths for reporting / extraction
    inst, class_refs = instance_tree(rf)
    replace = {}
    for (pc, i, _), (src, info) in zip(jobs, results):
        replace[(id(pc.chunk), i)] = src.encode("utf-8")
        rep.scripts += 1
        rep.functions += info["functions"]
        rep.failed_functions += info["failed"]
        rep.problems += len(info["problems"])
        refs = class_refs.get(pc.class_id, [])
        spath = "/".join(instance_path(inst, refs[i])) if i < len(refs) else "?"
        for fn, msg in info["errors"]:
            rep.errors.append((spath, fn, msg))
        for msg in info["problems"]:
            rep.errors.append((spath, "check", msg))

    for pc in rf.string_props():
        if pc.type != PT_PROTECTED_STRING and pc.name != "Source":
            continue
        vals = pc.values()
        changed = False
        for i in range(len(vals)):
            key = (id(pc.chunk), i)
            if key in replace:
                vals[i] = replace[key]
                changed = True
            elif pc.name == "Source":
                rep.text_sources += 1
        if changed or pc.type == PT_PROTECTED_STRING:
            pc.set_values(vals, PT_STRING)
            rep.converted_props += 1

    if not keep_signature:
        kept = []
        for ch in rf.chunks:
            if ch.name in SIGNATURE_CHUNKS:
                rep.removed_chunks.append(ch.name)
            else:
                kept.append(ch)
        rf.chunks = kept

    if out_path:
        os.makedirs(os.path.dirname(os.path.abspath(out_path)), exist_ok=True)
        rf.save(out_path)
    if extract_dir:
        extract_sources(rf, inst, class_refs, extract_dir)
    return rep


_SCRIPT_EXT = {"Script": ".server.lua", "LocalScript": ".client.lua", "ModuleScript": ".lua"}


def extract_sources(rf, inst, class_refs, out_dir):
    """Write every script's Source to out_dir mirroring the instance tree."""
    used = set()
    for pc in rf.string_props():
        if pc.name != "Source":
            continue
        refs = class_refs.get(pc.class_id, [])
        for i, v in enumerate(pc.values()):
            if i >= len(refs):
                continue
            parts = [_safe(p) for p in instance_path(inst, refs[i])]
            rel = os.path.join(*parts) if parts else "script"
            p = rel + _SCRIPT_EXT.get(pc.class_name, ".lua")
            n = 2
            base = p
            while p.lower() in used:
                p = base.replace(".", " (%d)." % n, 1) if "." in os.path.basename(base) else base + str(n)
                n += 1
            used.add(p.lower())
            full = os.path.join(out_dir, p)
            os.makedirs(os.path.dirname(full) or ".", exist_ok=True)
            with open(full, "wb") as f:
                f.write(v)


def _safe(name):
    bad = '<>:"/\\|?*'
    s = "".join("_" if c in bad or ord(c) < 32 else c for c in name).strip().rstrip(".")
    if s.upper() in ("CON", "PRN", "AUX", "NUL") or s.upper()[:3] in ("COM", "LPT") and s[3:].isdigit():
        s = "_" + s
    return s or "_"
