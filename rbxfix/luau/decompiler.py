"""Luau bytecode -> Luau source decompiler (entry point)."""
import os
import sys

DEBUG = bool(os.environ.get("RBXFIX_DEBUG"))

from . import bytecode as BC
from . import opcodes as O
from .ast import Comment, Return
from .cfg import DecompileError, Lifter
from .dataflow import analyze
from .emit import Emitter, fmt_string
from .fold import fold_block
from .passes import inline_single_use, simplify
from .scope import BUILTINS, KEYWORDS, enforce_local_limit, name_webs, place_declarations
from .structure import Structurer
from .ternary import TernaryRecovery

# globals the emitter itself may reference
EMITTED_GLOBALS = {"table", "select", "math", "Vector3", "getfenv", "error"}

HEADER = "-- Decompiled from Luau bytecode (version %d) by rbxfix\n"


class FunctionInfo:
    def __init__(self, script, proto, parent):
        self.script = script
        self.bc = script.bc
        self.proto = proto
        self.parent = parent
        self.capture_types = []
        self.upval_names = []
        self.param_webs = []
        self.entry_undefined = []
        self.is_method = False
        self.local_function_name = False
        self.names = set()
        self.body = None
        self.error = None
        self.analyzed = False
        self._children = {}

    def child(self, pid):
        c = self._children.get(pid)
        if c is None:
            if pid >= len(self.bc.protos):
                raise DecompileError("closure references unknown function %d" % pid)
            c = FunctionInfo(self.script, self.bc.protos[pid], self)
            self._children[pid] = c
        return c

    @property
    def label(self):
        return self.proto.debugname or "anonymous"


class ScriptDecompiler:
    def __init__(self, bc):
        self.bc = bc
        self.stats = {"functions": 0, "failed": 0, "errors": []}
        self.reserved = set(KEYWORDS) | set(BUILTINS) | self._global_names()

    def _global_names(self):
        names = set()
        for p in self.bc.protos:
            K = p.constants
            for ins in p.insns:
                op = ins.op
                try:
                    if op in (O.GETGLOBAL, O.SETGLOBAL):
                        names.add(K[ins.aux].value.decode("utf-8", "replace"))
                    elif op == O.GETIMPORT:
                        names.add(K[(ins.aux >> 20) & 1023].value.decode("utf-8", "replace"))
                except Exception:
                    pass
        return names

    # ---------------------------------------------------------- analysis
    def analyze(self, fn, reserved):
        if fn.analyzed:
            return
        fn.analyzed = True
        self.stats["functions"] += 1
        try:
            blocks = Lifter(fn).run()
            rpo, webs = analyze(fn, blocks)
            for b in rpo:
                fold_block(b)
            rpo = TernaryRecovery(rpo, webs).run()
            body = Structurer(rpo).structure()
            body = simplify(body)
            if body and type(body[-1]) is Return and not body[-1].values:
                body.pop()
            inline_single_use(body)
            declared = place_declarations(fn, body, webs)
            namer = name_webs(fn, body, declared, reserved)
            enforce_local_limit(fn, body, namer)
            fn.body = body
        except DecompileError as e:
            if DEBUG:
                raise
            fn.error = str(e)
        except RecursionError:
            fn.error = "function too deeply nested"
        except Exception as e:  # defensive: never crash the whole script
            fn.error = "internal error: %s: %s" % (type(e).__name__, e)
        if fn.error is not None:
            self.stats["failed"] += 1
            self.stats["errors"].append(("%s#%d" % (fn.label, fn.proto.index), fn.error))
            fn.names = set()
            fn.param_webs = []

    def emit_function(self, fn, upval_names, indent, name=None):
        """Return text `[name](params)\\n body \\n end` for a nested function."""
        parent = fn.parent
        if not fn.analyzed:
            fn.reserved_all = (parent.names | parent.reserved_all) if parent is not None else self.reserved
            self.analyze(fn, fn.reserved_all)
        fn.upval_names = list(upval_names)
        p = fn.proto
        if fn.error is not None:
            params = ", ".join("_" for _ in range(p.numparams))
            if p.is_vararg:
                params = (params + ", ..." if params else "...")
            msg = "decompilation of function '%s' failed: %s" % (fn.label, fn.error)
            body = ["\t" * (indent + 1) + "error(%s)" % fmt_string(msg)]
        else:
            params = [w.name for w in fn.param_webs]
            if p.is_vararg:
                params.append("...")
            params = ", ".join(params)
            em = Emitter(self)
            em.indent = indent + 1
            em.block(fn.body)
            body = em.lines
        head = ("%s(%s)" % (name, params)) if name else ("function(%s)" % params)
        return head + "\n" + "".join(l + "\n" for l in body) + "\t" * indent + "end"

    def run(self):
        main = FunctionInfo(self, self.bc.main_proto, None)
        main.reserved_all = self.reserved
        self.analyze(main, self.reserved)
        if main.error is not None:
            raise DecompileError("main chunk: " + main.error)
        em = Emitter(self)
        em.block(main.body)
        return "\n".join(em.lines) + "\n"


def decompile(data, header=True):
    """Decompile a Luau bytecode blob. Returns (source, stats)."""
    bc = BC.parse(data)
    sd = ScriptDecompiler(bc)
    src = sd.run()
    sd.stats["globals"] = sd._global_names() | EMITTED_GLOBALS
    if header:
        src = (HEADER % bc.version) + src
    return src, sd.stats


def disassemble(data):
    """Human readable listing of a bytecode blob (for debugging)."""
    bc = BC.parse(data)
    out = []
    for p in bc.protos:
        out.append("function %d %s (params=%d, ups=%d, vararg=%s, stack=%d) children=%s" % (
            p.index, p.debugname, p.numparams, p.nups, p.is_vararg, p.maxstacksize, p.children))
        for ins in p.insns:
            extra = ""
            if ins.aux is not None:
                extra = " aux=%d" % ins.aux
            out.append("  %4d  %-14s A=%-3d B=%-3d C=%-3d D=%-6d%s" % (
                ins.pc, ins.name, ins.a, ins.b, ins.c, ins.d, extra))
        for i, k in enumerate(p.constants):
            out.append("  K%d = %r" % (i, k))
    out.append("main = %d" % bc.main)
    return "\n".join(out)
