# Roblox Studio: Built-in plugin decompiler
(rbxfix for shorthand)

Open Roblox Studio's internal plugin files (`.rbxm` / `.rbxl`) that Studio otherwise refuses with *"Unable to open model … The file is corrupted."*. Result comes back with openable files to allow you to inspect with readable, editable Luau sources. 

Studio's built-in plugins ship signed and [pre-compiled to bytecode.](https://devforum.roblox.com/t/let-us-read-and-fork-the-built-in-plugins-again/2231981/5)

> **No Roblox files are included in this repository.** The plugin files are Roblox's property.
> Use copies from your own Studio installation and don't redistribute them, or the code decompiled from them.
> See [Legal](#legal).

Find these files in:
* `%LocalAppData%/Roblox/Versions/version-\*/BuiltInStandalonePlugins/Optimized_Embedded_Signature/`
* `%LocalAppData%/Roblox Studio/BuiltInStandalonePlugins/Optimized_Embedded_Signature/`

## Requirements
* Python 3.9 or newer (Windows, macOS or Linux)
* `pip install -r requirements.txt` (`lz4` and `zstandard`, used for chunk compression)

## Usage
```
python fix_rbxl.py path/to/plugins             # every .rbxm / .rbxl in the folder -> ./fixed/
python fix_rbxl.py example.rbxm -o out         # one file -> ./out/
python fix_rbxl.py example.rbxm --extract src  # also write each script as a .lua file -> ./fixed/ & ./src/
```

| Options            |                                                                                                                                                             |
| ------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `-o, --output DIR` | output folder (default `./fixed`)                                                                                                                           |
| `-j, --jobs N`     | worker processes (default: all CPUs)                                                                                                                        |
| `--extract DIR`    | also write every script as a `.lua` file mirroring the instance tree. Naming: `*.server.lua` = Script, `*.client.lua` = LocalScript, `*.lua` = ModuleScript |
| `--check`          | validate the generated code with the built-in Luau checker                                                                                                  |
| `--report FILE`    | write details of any function that could not be decompiled                                                                                                  |
| `--keep-signature` | don't strip the `SIGN`/`HASH` chunks (for experiments)                                                                                                      |
| `--decompile BLOB` | decompile a raw Luau bytecode file to stdout                                                                                                                |

## Why Studio rejects these files
Studio's built-in plugin files use the normal binary model format, with two differences from files Studio writes itself:
* a **`SIGN`** chunk (Roblox's signature) and usually a **`HASH`** chunk. Studio only accepts these when it loads its own plugins;
* script `Source` stored as property type `0x1D` (*ProtectedString*) containing **compiled Luau bytecode** instead of text.

## What rbxfix does
1. Decompiles every bytecode `Source` into Luau source.
2. Stores ProtectedString properties as ordinary strings (type `0x01`, what Studio writes).
3. Removes the `SIGN` and `HASH` chunks.
4. Leaves everything else byte-for-byte unchanged (instances, hierarchy, all other properties) and saves with LZ4 compression, as Studio does.

If a single function can't be decompiled, the file is still produced. That function becomes a stub that raises an error when called, and the problem is listed in the report.

In development, the tool was run on a full set of Studio built-in plugins: 111 files, ~317,000 scripts, ~1.49 million functions.
Every function decompiled, and all output passed the built-in Luau syntax and scope checker.

## How the decompiler works (`rbxfix/luau/`)
The plugins use Luau bytecode version 9; the parser supports versions 3 through 14.
Local variable names are not stored in the bytecode, so variables get generated names (`v1`, `tbl2`, `arg1`, …).
Where the code makes it obvious, better names are inferred:
- `require(x.Foo)` → `Foo`
- `game:GetService("Players")` → `Players`
- function names come from their debug names

| module         | job                                                                                                                                                                                                                     |
| -------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `bytecode.py`  | bytecode parser (mirrors Luau's `lvmload.cpp`)                                                                                                                                                                          |
| `cfg.py`       | splits functions into basic blocks and lifts instructions to an expression IR                                                                                                                                           |
| `dataflow.py`  | reaching definitions: groups register writes and reads into variables. Captured locals follow Luau's close-upvalue semantics, so closures created in loops capture a fresh variable per iteration                       |
| `fold.py`      | inlines single-use temporaries while keeping the exact evaluation order, and rebuilds table constructors                                                                                                                |
| `ternary.py`   | recovers `a and b`, `a or b` and `if c then x else y` value expressions                                                                                                                                                 |
| `structure.py` | rebuilds `if/elseif/else`, `while`, `repeat … until`, numeric and generic `for`, `break` and `continue` from per-loop post-dominators. Handles jump threading and the multi-exit loops left behind by function inlining |
| `passes.py`    | readability rewrites that preserve semantics (De Morgan in conditions, `x = a < b`, late inlining)                                                                                                                      |
| `scope.py`     | places each `local` in the innermost correct scope and names variables. Respects Luau's 200-local limit (silly)                                                                                                         |
| `emit.py`      | prints Luau: precedence, string escapes, interpolated strings, `function a.b()` sugar, and truncation `(f())` where a call's results were cut to one                                                                    |
| `checker.py`   | independent Luau parser used to validate output: syntax, undefined names, local limits                                                                                                                                  |

Every transformation is chosen to preserve semantics exactly. Where a construct can't be written without `goto` (missing in Luau), the code is duplicated or a flag variable is introduced. Nothing is approximated.

## Limitations
* The output has been validated with the built-in checker, not with Roblox's own Luau compiler.
* Open fixed files in Studio to confirm them before relying on them.
* Studio's built-in plugins are compiled with `-O2`, so small functions have been inlined. You will sometimes see a helper's body written out several times instead of a simple call.
* Many built-in plugins use Studio internal APIs (e.g. `StandalonePluginScripts`). They open and can be read and edited, but won't run as ordinary user plugins (if that is your goal).

## Tests
```
pip install pytest
python -m pytest tests # or: python tests/test_rbxfix.py
```

The tests build bytecode and model files in memory, so they need no external files and run anywhere.

## Legal
This project is not affiliated with or endorsed by Roblox Corporation.
It's meant for inspecting and editing plugin files you already have on your own machine, for interoperability and learning.
Check the Roblox Terms of Use before redistributing anything it produces.
