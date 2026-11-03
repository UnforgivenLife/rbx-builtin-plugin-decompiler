"""Independent Luau syntax + scope checker used to validate decompiler output.

It parses the (type-annotation free) Luau subset produced by the decompiler and
reports:
  * syntax errors
  * names that are neither a visible local nor an expected global
  * functions exceeding Luau's limit of 200 active locals
"""
import re

KEYWORDS = {"and", "break", "do", "else", "elseif", "end", "false", "for", "function", "if",
            "in", "local", "nil", "not", "or", "repeat", "return", "then", "true", "until",
            "while"}

_TOKEN = re.compile(r"""
    (?P<ws>[ \t\r\n]+) |
    (?P<comment>--\[(?P<eq>=*)\[.*?\](?P=eq)\]|--[^\n]*) |
    (?P<name>[A-Za-z_][A-Za-z0-9_]*) |
    (?P<num>0[xX][0-9a-fA-F_]+|0[bB][01_]+|(?:[0-9][0-9_]*(?:\.[0-9_]*)?|\.[0-9][0-9_]*)(?:[eE][+-]?[0-9]+)?i?) |
    (?P<str>"(?:\\.|\\\n|[^"\\\n])*"|'(?:\\.|\\\n|[^'\\\n])*') |
    (?P<lstr>\[(?P<eq2>=*)\[.*?\](?P=eq2)\]) |
    (?P<op>\.\.\.|\.\.|==|~=|<=|>=|//|::|->|[-+*/%^#<>=(){}\[\];:,.])
""", re.S | re.X)


class LuauSyntaxError(Exception):
    pass


def tokenize(src):
    pos = 0
    line = 1
    out = []
    n = len(src)
    while pos < n:
        if src[pos] == "`":
            pos, line = _interp(src, pos, line, out)
            continue
        m = _TOKEN.match(src, pos)
        if not m:
            raise LuauSyntaxError("line %d: unexpected character %r" % (line, src[pos]))
        kind = m.lastgroup
        text = m.group(0)
        if kind in ("eq", "eq2"):
            kind = "lstr" if m.group("lstr") else "comment"
        if m.group("ws") is not None:
            kind = "ws"
        elif m.group("comment") is not None:
            kind = "comment"
        elif m.group("name") is not None:
            kind = "kw" if text in KEYWORDS else "name"
        elif m.group("num") is not None:
            kind = "num"
        elif m.group("str") is not None or m.group("lstr") is not None:
            kind = "str"
        else:
            kind = "op"
        if kind not in ("ws", "comment"):
            out.append((kind, text, line))
        line += text.count("\n")
        pos = m.end()
    out.append(("eof", "", line))
    return out


def _skip_braces(src, j):
    """Index of the `}` closing an interpolation expression that starts at j."""
    n = len(src)
    depth = 1
    while j < n:
        ch = src[j]
        if ch in "\"'":
            q = ch
            j += 1
            while j < n and src[j] != q:
                j += 2 if src[j] == "\\" else 1
        elif ch == "`":
            j = _skip_interp(src, j)
            continue
        elif ch == "-" and src.startswith("--", j):
            while j < n and src[j] != "\n":
                j += 1
            continue
        elif ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return j
        j += 1
    raise LuauSyntaxError("unfinished interpolation expression")


def _skip_interp(src, j):
    """Index just past the interpolated string starting at src[j] == '`'."""
    n = len(src)
    j += 1
    while j < n:
        ch = src[j]
        if ch == "\\":
            j += 2
        elif ch == "`":
            return j + 1
        elif ch == "{":
            j = _skip_braces(src, j + 1) + 1
        else:
            j += 1
    raise LuauSyntaxError("unfinished interpolated string")


def _interp(src, pos, line, out):
    """Tokenize an interpolated string as ( "lit" .. (expr) .. "lit" ... )."""
    start_line = line
    pos += 1
    out.append(("op", "(", line))
    first = True
    n = len(src)
    while True:
        if pos >= n:
            raise LuauSyntaxError("line %d: unfinished interpolated string" % start_line)
        c = src[pos]
        if c == "\\":
            pos += 2
            continue
        if c == "\n":
            raise LuauSyntaxError("line %d: newline in interpolated string" % line)
        if c == "`":
            pos += 1
            break
        if c == "{":
            j = _skip_braces(src, pos + 1)
            inner = tokenize(src[pos + 1:j])[:-1]
            if not inner:
                raise LuauSyntaxError("line %d: empty interpolation" % line)
            if not first:
                out.append(("op", "..", line))
            out.append(("op", "(", line))
            out.extend((k, t, line) for k, t, _ in inner)
            out.append(("op", ")", line))
            first = False
            pos = j + 1
            continue
        pos += 1
    if first:
        out.append(("str", '""', line))
    out.append(("op", ")", line))
    return pos, line


class _Func:
    def __init__(self, parent):
        self.parent = parent
        self.scopes = [set()]
        self.active = 0
        self.max_active = 0
        self.counts = [0]

    def declare(self, name):
        self.scopes[-1].add(name)
        self.counts[-1] += 1
        self.active += 1
        self.max_active = max(self.max_active, self.active)

    def push(self):
        self.scopes.append(set())
        self.counts.append(0)

    def pop(self):
        self.scopes.pop()
        self.active -= self.counts.pop()

    def visible(self, name):
        f = self
        while f is not None:
            for s in f.scopes:
                if name in s:
                    return True
            f = f.parent
        return False


class Checker:
    def __init__(self, src, globals_ok=None, max_locals=200):
        self.toks = tokenize(src)
        self.i = 0
        self.globals_ok = globals_ok
        self.max_locals = max_locals
        self.problems = []
        self.fn = None

    # ---------------------------------------------------------- tokens
    def peek(self, k=0):
        return self.toks[self.i + k]

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def check(self, text):
        t = self.toks[self.i]
        return t[1] == text and t[0] in ("op", "kw")

    def accept(self, text):
        if self.check(text):
            self.i += 1
            return True
        return False

    def expect(self, text):
        t = self.next()
        if t[1] != text or t[0] not in ("op", "kw"):
            raise LuauSyntaxError("line %d: expected %r near %r" % (t[2], text, t[1]))
        return t

    def name(self):
        t = self.next()
        if t[0] != "name":
            raise LuauSyntaxError("line %d: expected name near %r" % (t[2], t[1]))
        return t[1]

    # --------------------------------------------------------- driver
    def run(self):
        self.fn = _Func(None)
        self.fn.declare("...")
        self.block()
        t = self.peek()
        if t[0] != "eof":
            raise LuauSyntaxError("line %d: unexpected %r" % (t[2], t[1]))
        self._finish_fn()
        return self.problems

    def _finish_fn(self):
        if self.fn.max_active > self.max_locals:
            self.problems.append("function uses %d locals (limit %d)" % (self.fn.max_active, self.max_locals))

    def use(self, name, line):
        if self.fn.visible(name):
            return
        if self.globals_ok is not None and name not in self.globals_ok:
            self.problems.append("line %d: '%s' is not a visible local or a known global" % (line, name))

    # ------------------------------------------------------- statements
    def block_end(self):
        t = self.peek()
        return t[0] == "eof" or (t[0] == "kw" and t[1] in ("end", "else", "elseif", "until"))

    def block(self):
        while not self.block_end():
            if self.check("return"):
                self.next()
                if not self.block_end() and not self.check(";"):
                    self.exprlist()
                self.accept(";")
                if not self.block_end():
                    t = self.peek()
                    raise LuauSyntaxError("line %d: statement after return" % t[2])
                return
            if self.check("break") or (self.peek()[0] == "name" and self.peek()[1] == "continue"
                                         and self._continue_stmt()):
                self.next()
                self.accept(";")
                if not self.block_end():
                    t = self.peek()
                    raise LuauSyntaxError("line %d: statement after break/continue" % t[2])
                return
            self.statement()
            self.accept(";")

    def _continue_stmt(self):
        nxt = self.peek(1)
        return nxt[0] in ("kw", "eof") and nxt[1] in ("end", "else", "elseif", "until", "")

    def statement(self):
        t = self.peek()
        if t[0] == "op" and t[1] == ";":
            self.next()
            return
        if t[0] == "kw":
            k = t[1]
            if k == "if":
                self.next()
                self.expr()
                self.expect("then")
                self.scoped_block()
                while self.accept("elseif"):
                    self.expr()
                    self.expect("then")
                    self.scoped_block()
                if self.accept("else"):
                    self.scoped_block()
                self.expect("end")
                return
            if k == "while":
                self.next()
                self.expr()
                self.expect("do")
                self.scoped_block()
                self.expect("end")
                return
            if k == "do":
                self.next()
                self.scoped_block()
                self.expect("end")
                return
            if k == "repeat":
                self.next()
                self.fn.push()
                self.block()
                self.expect("until")
                self.expr()
                self.fn.pop()
                return
            if k == "for":
                self.next()
                n1 = self.name()
                if self.accept("="):
                    self.expr()
                    self.expect(",")
                    self.expr()
                    if self.accept(","):
                        self.expr()
                    names = [n1]
                else:
                    names = [n1]
                    while self.accept(","):
                        names.append(self.name())
                    self.expect("in")
                    self.exprlist()
                self.expect("do")
                self.fn.push()
                for n in names:
                    self.fn.declare(n)
                self.block()
                self.fn.pop()
                self.expect("end")
                return
            if k == "function":
                self.next()
                line = self.peek()[2]
                n = self.name()
                self.use(n, line)
                is_method = False
                while self.check(".") or self.check(":"):
                    if self.next()[1] == ":":
                        is_method = True
                    self.name()
                    if is_method:
                        break
                self.funcbody(is_method)
                return
            if k == "local":
                self.next()
                if self.accept("function"):
                    n = self.name()
                    self.fn.declare(n)
                    self.funcbody(False)
                    return
                names = [self.name()]
                while self.accept(","):
                    names.append(self.name())
                if self.accept("="):
                    self.exprlist()
                for n in names:
                    self.fn.declare(n)
                return
            raise LuauSyntaxError("line %d: unexpected %r" % (t[2], t[1]))
        # expression statement: call or assignment
        targets = [self.suffixedexp()]
        if self.check("=") or self.check(","):
            while self.accept(","):
                targets.append(self.suffixedexp())
            for tk in targets:
                if tk not in ("name", "index"):
                    raise LuauSyntaxError("line %d: cannot assign to expression" % t[2])
            self.expect("=")
            self.exprlist()
        else:
            if targets[0] != "call":
                raise LuauSyntaxError("line %d: syntax error near %r" % (self.peek()[2], self.peek()[1]))

    def scoped_block(self):
        self.fn.push()
        self.block()
        self.fn.pop()

    def funcbody(self, is_method):
        parent = self.fn
        self.fn = _Func(parent)
        if is_method:
            self.fn.declare("self")
        self.expect("(")
        if not self.check(")"):
            while True:
                if self.accept("..."):
                    self.fn.declare("...")
                    break
                self.fn.declare(self.name())
                if not self.accept(","):
                    break
        self.expect(")")
        self.block()
        self.expect("end")
        self._finish_fn()
        self.fn = parent

    # ------------------------------------------------------ expressions
    def exprlist(self):
        self.expr()
        while self.accept(","):
            self.expr()

    BINPRI = {"or": (1, 1), "and": (2, 2), "<": (3, 3), ">": (3, 3), "<=": (3, 3), ">=": (3, 3),
              "~=": (3, 3), "==": (3, 3), "..": (5, 4), "+": (6, 6), "-": (6, 6), "*": (7, 7),
              "/": (7, 7), "//": (7, 7), "%": (7, 7), "^": (10, 9)}
    UNARY_PRI = 8

    def expr(self, limit=0):
        t = self.peek()
        if t[0] == "kw" and t[1] == "if":
            self.next()
            self.expr()
            self.expect("then")
            self.expr()
            while self.accept("elseif"):
                self.expr()
                self.expect("then")
                self.expr()
            self.expect("else")
            self.expr()
            return
        if (t[0] == "kw" and t[1] == "not") or (t[0] == "op" and t[1] in ("-", "#")):
            self.next()
            self.expr(self.UNARY_PRI)
        else:
            self.simpleexp()
        while True:
            t = self.peek()
            if t[0] not in ("op", "kw") or t[1] not in self.BINPRI:
                break
            left, right = self.BINPRI[t[1]]
            if left <= limit:
                break
            self.next()
            self.expr(right)

    def simpleexp(self):
        t = self.peek()
        if t[0] in ("num", "str"):
            self.next()
            return
        if t[0] == "kw" and t[1] in ("nil", "true", "false"):
            self.next()
            return
        if t[0] == "op" and t[1] == "...":
            self.next()
            if not self.fn.visible("...") or "..." not in self.fn.scopes[0]:
                raise LuauSyntaxError("line %d: '...' outside a vararg function" % t[2])
            return
        if t[0] == "op" and t[1] == "{":
            self.table()
            return
        if t[0] == "kw" and t[1] == "function":
            self.next()
            self.funcbody(False)
            return
        self.suffixedexp()

    def table(self):
        self.expect("{")
        while not self.check("}"):
            if self.check("["):
                self.next()
                self.expr()
                self.expect("]")
                self.expect("=")
                self.expr()
            elif self.peek()[0] == "name" and self.peek(1)[1] == "=" and self.peek(1)[0] == "op":
                self.next()
                self.next()
                self.expr()
            else:
                self.expr()
            if not (self.accept(",") or self.accept(";")):
                break
        self.expect("}")

    def primaryexp(self):
        t = self.next()
        if t[0] == "name":
            self.use(t[1], t[2])
            return "name"
        if t[0] == "op" and t[1] == "(":
            self.expr()
            self.expect(")")
            return "paren"
        raise LuauSyntaxError("line %d: unexpected %r" % (t[2], t[1]))

    def suffixedexp(self):
        kind = self.primaryexp()
        while True:
            t = self.peek()
            if t[0] != "op" and t[0] != "str":
                break
            if t[1] == ".":
                self.next()
                self.name()
                kind = "index"
            elif t[1] == "[":
                self.next()
                self.expr()
                self.expect("]")
                kind = "index"
            elif t[1] == ":":
                self.next()
                self.name()
                self.callargs()
                kind = "call"
            elif t[1] in ("(", "{") or t[0] == "str":
                self.callargs()
                kind = "call"
            else:
                break
        return kind

    def callargs(self):
        t = self.peek()
        if t[0] == "str":
            self.next()
        elif t[1] == "{":
            self.table()
        else:
            self.expect("(")
            if not self.check(")"):
                self.exprlist()
            self.expect(")")


def check_source(src, globals_ok=None):
    """Return a list of problems (empty if the source looks valid)."""
    try:
        return Checker(src, globals_ok).run()
    except LuauSyntaxError as e:
        return ["syntax error: %s" % e]
    except RecursionError:
        return ["checker recursion limit"]
