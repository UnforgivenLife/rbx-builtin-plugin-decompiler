#!/usr/bin/env python3
"""Fix Roblox model/place files that Studio refuses to open ("The file is corrupted").

Usage examples:
    python fix_rbxl.py path/to/plugins              # fixes every file -> ./fixed/
    python fix_rbxl.py Footer.rbxm -o out
    python fix_rbxl.py path/to/plugins --extract sources   # also dump decompiled .lua files
    python fix_rbxl.py --decompile some_bytecode.bin   # decompile a raw bytecode blob

See README.md for details.
"""
import argparse
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from rbxfix.fixer import decompile_batch, fix_file  # noqa: E402

EXTS = (".rbxm", ".rbxl")


def _pool_worker(args):
    blobs, check = args
    return decompile_batch(blobs, check)


def gather_inputs(paths):
    files = []
    for p in paths:
        if os.path.isdir(p):
            for root, _, names in os.walk(p):
                for n in sorted(names):
                    if n.lower().endswith(EXTS):
                        files.append(os.path.join(root, n))
        elif os.path.isfile(p):
            files.append(p)
        else:
            print("warning: %s not found" % p, file=sys.stderr)
    return files


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("inputs", nargs="*", help="files or folders (.rbxm/.rbxl)")
    ap.add_argument("-o", "--output", default="fixed", help="output folder (default: ./fixed)")
    ap.add_argument("-j", "--jobs", type=int, default=0, help="worker processes (default: all CPUs)")
    ap.add_argument("--extract", metavar="DIR", help="also write decompiled scripts as .lua files")
    ap.add_argument("--check", action="store_true", help="validate decompiled code with the built-in Luau checker")
    ap.add_argument("--keep-signature", action="store_true", help="do not remove SIGN/HASH chunks")
    ap.add_argument("--report", metavar="FILE", help="write per-function failure details to FILE")
    ap.add_argument("--decompile", metavar="BLOB", help="decompile a raw Luau bytecode file to stdout")
    args = ap.parse_args(argv)

    if args.decompile:
        with open(args.decompile, "rb") as f:
            blob = f.read()
        (src, info), = decompile_batch([blob])
        sys.stdout.write(src)
        return 0 if not info["failed"] else 1

    files = gather_inputs(args.inputs)
    if not files:
        ap.print_help()
        return 2

    jobs = args.jobs or os.cpu_count() or 1
    pool = None
    if jobs > 1:
        import multiprocessing
        pool = multiprocessing.Pool(jobs)

    def parallel_decompile(blobs):
        if pool is None or len(blobs) < 8:
            return decompile_batch(blobs, args.check)
        # balance: ~4 chunks per worker, sized by bytecode volume
        target = max(1, sum(len(b) for b in blobs) // (jobs * 4))
        chunks, cur, size = [], [], 0
        for b in blobs:
            cur.append(b)
            size += len(b)
            if size >= target:
                chunks.append(cur)
                cur, size = [], 0
        if cur:
            chunks.append(cur)
        out = []
        for part in pool.map(_pool_worker, [(c, args.check) for c in chunks]):
            out.extend(part)
        return out

    t0 = time.time()
    totals = {"files": 0, "scripts": 0, "functions": 0, "failed": 0}
    report_lines = []
    base_inputs = [os.path.abspath(p) for p in args.inputs if os.path.isdir(p)]
    try:
        for path in files:
            rel = os.path.basename(path)
            ap_ = os.path.abspath(path)
            for b in base_inputs:
                if ap_.startswith(b + os.sep):
                    rel = os.path.relpath(ap_, b)
            out_path = os.path.join(args.output, rel)
            extract = os.path.join(args.extract, os.path.splitext(rel)[0]) if args.extract else None
            t = time.time()
            try:
                rep = fix_file(path, out_path, parallel_decompile, args.check, extract, args.keep_signature)
            except Exception as e:
                print("FAILED %s: %s" % (path, e))
                continue
            totals["files"] += 1
            totals["scripts"] += rep.scripts
            totals["functions"] += rep.functions
            totals["failed"] += rep.failed_functions
            print("%s  [%.1fs] -> %s" % (rep.summary(), time.time() - t, out_path))
            for spath, fn, msg in rep.errors:
                report_lines.append("%s\t%s\t%s\t%s" % (rel, spath, fn, msg))
    finally:
        if pool is not None:
            pool.close()
            pool.join()

    ok = totals["functions"] - totals["failed"]
    pct = (100.0 * ok / totals["functions"]) if totals["functions"] else 100.0
    print("\nDone: %d files, %d scripts, %d/%d functions decompiled (%.3f%%) in %.0fs"
          % (totals["files"], totals["scripts"], ok, totals["functions"], pct, time.time() - t0))
    if report_lines:
        if args.report:
            with open(args.report, "w", encoding="utf-8") as f:
                f.write("file\tscript\tfunction\tproblem\n")
                f.write("\n".join(report_lines) + "\n")
            print("Details of %d problem(s) written to %s" % (len(report_lines), args.report))
        else:
            print("%d function(s) could not be decompiled; they raise an error when called. "
                  "Use --report FILE for details." % len(report_lines))
    return 0


if __name__ == "__main__":
    sys.exit(main())
