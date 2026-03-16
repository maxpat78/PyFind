"""
pyfind.py 0.20

This module provides a simple tool to search a directory tree for files
matching some criteria, in a way similar to GNU find.

A sample:
    from pyfind import Search

    # Finds all files greater than 1 MiB, created in the last 25 minutes,
    # whose name ends in '.py' or '.pyc'
    for found in Search('.', '-size +1m -a -cmin -25 -a ( -name *.py -o -name *.pyc )').find():
        print(found)

Supported switches:
    -size, -adate/-cdate/-mdate, -ahour/-chour/-mhour,
    -atime/-ctime/-mtime, -amin/-cmin/-mmin, -anewer/-cnewer/-mnewer,
    -mindepth, -maxdepth, -name/-iname, -path/-ipath/-wholename/-iwholename,
    -regex/-iregex, -type, -daystart,
    -and/-a, -or/-o, -not/-!, -true, -false

Changes from 0.14:
    - Replaced eval()/exec() with a safe AST-based expression engine
    - Fixed depth() to use os.path.relpath (works on Linux, macOS, Windows)
    - Fixed stat attribute access via st_atime/st_mtime/st_ctime names
    - Guarded against expr=None
    - Fixed findall() calling find(with_stat=True) explicitly
    - Coerce size multiplier operand to float
    - Renamed 'p' -> 'self' throughout for PEP-8 compliance
    - Added -! as alias for -not, -a as alias for -and, -o as alias for -or
    - Added -print, -ls, -maxdepth/-mindepth as top-level GNU aliases
    - Improved implicit 'and' insertion logic
    - Type hints and docstrings on all public methods
"""

import sys
import ast
import datetime
import fnmatch
import os
import operator
import re
import shlex
import time
import functools
import stat
import logging
from typing import Iterator, Union


# ---------------------------------------------------------------------------
# Sort constants
# ---------------------------------------------------------------------------
NO_SORT       = -1
SORT_PATHNAME =  0
SORT_NAME     =  1
SORT_EXT      =  2
SORT_SIZE     =  3
SORT_ATIME    =  4
SORT_CTIME    =  5
SORT_MTIME    =  6


# ---------------------------------------------------------------------------
# Safe expression engine
#
# Instead of building a Python source string and calling eval(), we build a
# tiny AST of callable nodes.  Each node is a Python callable that accepts
# no arguments and closes over whatever it needs from the enclosing Search
# instance (passed as 'ctx').
# ---------------------------------------------------------------------------

class _Node:
    """Base class for expression tree nodes."""
    def __call__(self, ctx: "Search") -> bool:
        raise NotImplementedError


class _Const(_Node):
    def __init__(self, value: bool):
        self.value = value
    def __call__(self, ctx):
        return self.value


class _And(_Node):
    def __init__(self, left: _Node, right: _Node):
        self.left, self.right = left, right
    def __call__(self, ctx):
        return self.left(ctx) and self.right(ctx)


class _Or(_Node):
    def __init__(self, left: _Node, right: _Node):
        self.left, self.right = left, right
    def __call__(self, ctx):
        return self.left(ctx) or self.right(ctx)


class _Not(_Node):
    def __init__(self, operand: _Node):
        self.operand = operand
    def __call__(self, ctx):
        return not self.operand(ctx)


class _Predicate(_Node):
    """Wraps a bound method call with pre-bound arguments."""
    def __init__(self, method_name: str, *args):
        self.method_name = method_name
        self.args = args
    def __call__(self, ctx):
        return getattr(ctx, self.method_name)(*self.args)


# ---------------------------------------------------------------------------
# Token → AST parser  (recursive-descent, operator precedence)
#
# Grammar:
#   expr   ::= term ( ('-or'|'-o') term )*
#   term   ::= factor ( ('-and'|'-a'|implicit) factor )*
#   factor ::= '-not' factor | '-!' factor | '(' expr ')' | primary
#   primary::= <predicate switch with optional argument>
# ---------------------------------------------------------------------------

_BOOL_OPS = frozenset({'-and', '-a', '-or', '-o', '-not', '-!'})
_OPEN_PAREN  = '('
_CLOSE_PAREN = ')'


class _Parser:
    def __init__(self, tokens: list[str], search: "Search"):
        self.tokens  = tokens
        self.pos     = 0
        self.search  = search   # needed for _daystart side-effect only

    # ------------------------------------------------------------------
    def _peek(self) -> str | None:
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def _consume(self) -> str:
        t = self.tokens[self.pos]
        self.pos += 1
        return t

    def _consume_arg(self, switch: str) -> str:
        if self.pos >= len(self.tokens):
            raise SyntaxError(f"Switch '{switch}' requires an argument")
        return self._consume()

    # ------------------------------------------------------------------
    def parse(self) -> _Node:
        node = self._expr()
        if self.pos < len(self.tokens):
            raise SyntaxError(f"Unexpected token '{self.tokens[self.pos]}'")
        return node

    def _expr(self) -> _Node:
        """expr ::= term ( ('-or'|'-o') term )*"""
        node = self._term()
        while self._peek() in ('-or', '-o'):
            self._consume()
            node = _Or(node, self._term())
        return node

    def _term(self) -> _Node:
        """term ::= factor ( implicit-and factor )*"""
        node = self._factor()
        while self._peek() not in (None, '-or', '-o', _CLOSE_PAREN):
            # consume explicit '-and'/'-a', otherwise it's implicit
            if self._peek() in ('-and', '-a'):
                self._consume()
            node = _And(node, self._factor())
        return node

    def _factor(self) -> _Node:
        """factor ::= ('-not'|'-!') factor | '(' expr ')' | primary"""
        t = self._peek()
        if t in ('-not', '-!'):
            self._consume()
            return _Not(self._factor())
        if t == _OPEN_PAREN:
            self._consume()
            node = self._expr()
            if self._peek() != _CLOSE_PAREN:
                raise SyntaxError("Missing closing ')'")
            self._consume()
            return node
        return self._primary()

    def _primary(self) -> _Node:
        """Map a switch (and optional argument) to a _Node."""
        t = self._peek()
        if t is None:
            raise SyntaxError("Unexpected end of expression")

        # -true / -false
        if t == '-true':
            self._consume()
            return _Const(True)
        if t == '-false':
            self._consume()
            return _Const(False)

        # -daystart  (side-effect on the Search instance, returns -true)
        if t == '-daystart':
            self._consume()
            self.search.NOW = self.search.NOW.replace(
                hour=0, minute=0, second=0, microsecond=0)
            # Align the epoch reference to midnight as well
            midnight = self.search.NOW
            self.search._now_epoch = midnight.timestamp()
            return _Const(True)

        # -print / -ls  (GNU find actions — just return True, output elsewhere)
        if t in ('-print', '-ls'):
            self._consume()
            return _Const(True)

        # -mindepth / -maxdepth
        m = re.fullmatch(r'-(min|max)depth', t)
        if m:
            self._consume()
            arg = self._consume_arg(t)
            if not re.fullmatch(r'\d+', arg):
                raise SyntaxError(f"Invalid depth value '{arg}' for '{t}'")
            kind = m.group(1)           # 'min' or 'max'
            setattr(self.search, kind + 'depth', int(arg))
            return _Const(True)

        # All other switches defined in _SWITCH_TABLE
        for pattern, nargs, arg_re, builder in _SWITCH_TABLE:
            m = re.fullmatch(pattern, t)
            if m:
                self._consume()
                sw_groups = m.groups()      # capture groups from the switch
                if nargs:
                    arg = self._consume_arg(t)
                    am = re.fullmatch(arg_re, arg)
                    if not am:
                        raise SyntaxError(
                            f"Wrong argument '{arg}' for switch '{t}'")
                    arg_groups = am.groups()
                else:
                    arg_groups = ()
                return builder(sw_groups, arg_groups)

        raise SyntaxError(f"Unknown switch '{t}'")


# ---------------------------------------------------------------------------
# Switch table
#
# Each entry: (switch_pattern, nargs, arg_pattern, builder)
# builder(sw_groups, arg_groups) -> _Node
# ---------------------------------------------------------------------------

def _B(method, *fixed_args):
    """Shorthand: build a _Predicate node."""
    return _Predicate(method, *fixed_args)


def _size_builder(sw, ag):
    op, n, m = ag[0] or '=', float(ag[1]), ag[2]
    return _Predicate('_size', op, n, m)

def _date_builder(sw, ag):
    typ = sw[0]
    op, dd, mm_d, yy = ag[0] or '=', int(ag[1]), int(ag[2]), int(ag[3])
    return _Predicate('_date', typ, op, dd, mm_d, yy)

def _hour_builder(sw, ag):
    typ = sw[0]
    op, hh, mm = ag[0] or '=', int(ag[1]), int(ag[2])
    return _Predicate('_hour', typ, op, hh, mm)

def _time_builder(sw, ag):
    typ = sw[0]
    op, n = ag[0] or '=', float(ag[1])
    return _Predicate('_time', typ, op, n)

def _min_builder(sw, ag):
    typ = sw[0]
    op, mm = ag[0] or '=', float(ag[1])
    return _Predicate('_time_min', typ, op, mm)

def _newer_builder(sw, ag):
    typ = sw[0]
    name = ag[0]
    return _Predicate('_newer', typ, name)

def _name_builder(sw, ag):
    case = sw[0]        # '' or 'i'
    pat = ag[0]
    method = '_iname' if case == 'i' else '_name'
    return _Predicate(method, pat)

def _wholename_builder(sw, ag):
    case = sw[0]
    pat = ag[1]
    method = '_iwholename' if case == 'i' else '_wholename'
    return _Predicate(method, pat)

def _regex_builder(sw, ag):
    case = sw[0]
    pat = ag[0]
    method = '_iregex' if case == 'i' else '_regex'
    return _Predicate(method, pat)

def _type_builder(sw, ag):
    return _Predicate('_type', ag[0])

def _empty_builder(sw, ag):
    return _Predicate('_empty')

def _executable_builder(sw, ag):
    return _Predicate('_executable')

def _readable_builder(sw, ag):
    return _Predicate('_readable')

def _writable_builder(sw, ag):
    return _Predicate('_writable')


_SWITCH_TABLE = [
    # (switch regex, nargs, arg regex, builder)
    (r'-size',              1, r'([+=-]?)([0-9.]+)([bcwkmgt]?)',                    _size_builder),
    (r'-([acm])date',       1, r'([+=-]?)(\d{1,2})[./](\d{1,2})[./](\d{2,4})',     _date_builder),
    (r'-([acm])hour',       1, r'([+=-]?)(\d{1,2})[:.](\d{1,2})',                  _hour_builder),
    (r'-([acm])time',       1, r'([+=-]?)([0-9]+\.?[0-9]*)',                        _time_builder),
    (r'-([acm])min',        1, r'([+=-]?)([0-9.]+)',                                _min_builder),
    (r'-([acm])newer',      1, r'(.+)',                                             _newer_builder),
    (r'-(i?)name',          1, r'(.+)',                                             _name_builder),
    (r'-(i?)(wholename|path)', 1, r'(.+)',                                          _wholename_builder),
    (r'-(i?)regex',         1, r'(.+)',                                             _regex_builder),
    (r'-type',              1, r'([dfl])',                                          _type_builder),
    (r'-empty',             0, r'',                                                 _empty_builder),
    (r'-executable',        0, r'',                                                 _executable_builder),
    (r'-readable',          0, r'',                                                 _readable_builder),
    (r'-writable',          0, r'',                                                 _writable_builder),
]


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _stat_time(st: os.stat_result, typ: str) -> float:
    """Return the appropriate timestamp from a stat result."""
    return {'a': st.st_atime, 'm': st.st_mtime, 'c': st.st_ctime}[typ]


def _op(op_str: str):
    """Translate '+'/'-'/'='  to an operator function."""
    return {'+': operator.gt, '-': operator.lt}.get(op_str, operator.eq)


def _cmp(a, b) -> int:
    return (a > b) - (a < b)


# ---------------------------------------------------------------------------
# Main Search class
# ---------------------------------------------------------------------------

class Search:
    """
    Search a directory tree for files/dirs matching a GNU find-style expression.

    Parameters
    ----------
    root : str
        Directory to start the search from.
    expr : str | None
        GNU find-style expression string.  Pass None or '' to match everything.
    """

    def __init__(self, root: str = '.', expr: str | None = None):
        self.DEBUG    = False
        self.dirs     = [root]
        self.names    = ['*']
        self.excludes: list[str] | None = None
        self.mindepth = -1
        self.maxdepth = -1
        self.NOW        = datetime.datetime.now().replace(microsecond=0)
        self._now_epoch = time.time()   # raw epoch; used by _time / _time_min
        self._expr_tree: _Node | None = None

        # Current file being evaluated (set inside _match)
        self._path: str = ''
        self._st:   os.stat_result | None = None

        if not expr:
            return  # no expression → match everything

        # shlex.split handles quoting and escaping, but parentheses attached
        # to adjacent tokens (e.g. "(-name" or "*.py)") are not separated.
        # We split each token further on '(' and ')' so that the parser
        # always sees them as standalone tokens, exactly like GNU find does
        # when bash passes \( and \) as individual arguments.
        raw = shlex.split(expr)
        tokens: list[str] = []
        for tok in raw:
            # Re-tokenize on parentheses while preserving them as tokens
            parts = re.split(r'(\(|\))', tok)
            tokens.extend(p for p in parts if p)
        if self.DEBUG:
            logging.debug('Tokens: %s', tokens)

        parser = _Parser(tokens, self)
        self._expr_tree = parser.parse()

        if self.DEBUG:
            logging.debug('mindepth=%d maxdepth=%d', self.mindepth, self.maxdepth)

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def find(self, with_stat: bool = False) -> Iterator:
        """
        Traverse the directory tree and yield matching pathnames.

        Parameters
        ----------
        with_stat : bool
            If True, yield (pathname, os.stat_result) tuples instead of
            plain pathnames.
        """
        for top in self.dirs:
            for root, dirs, files in os.walk(top, followlinks=False):
                d = self._depth(top, root)
                if self.maxdepth >= 0 and d > self.maxdepth:
                    # Prune subdirectories to avoid scanning deeper
                    dirs[:] = []
                    continue
                skip_shallow = self.mindepth >= 0 and d < self.mindepth

                entries = [(f, False) for f in files] + [(dn, True) for dn in dirs]
                for name, is_dir in entries:
                    pn = os.path.join(root, name)
                    if skip_shallow:
                        continue
                    if self._name_filter(pn) and self._match(pn):
                        if with_stat:
                            yield pn, os.stat(pn)
                        else:
                            yield pn

    def findall(self, with_stat: bool = False) -> dict | list:
        """
        Traverse the tree and return all matching pathnames.

        Returns
        -------
        dict {pathname: stat} if with_stat, else a list of pathnames.
        """
        found = dict(self.find(with_stat=True))
        if with_stat:
            return found
        return list(found.keys())

    def sortall(
        self,
        result: dict,
        sort_by: list[int],
        with_stat: bool = False,
    ) -> list:
        """
        Sort a dict returned by findall(with_stat=True).

        Parameters
        ----------
        result  : dict {pathname: stat}
        sort_by : list of SORT_* constants (applied in order)
        with_stat : if False, strip the stat from the returned list
        """
        if not isinstance(result, dict):
            raise TypeError("result must be a dict {pathname: stat} from findall()")
        self._sort_by = sort_by
        items = sorted(result.items(),
                       key=functools.cmp_to_key(self._sortcmp))
        if with_stat:
            return items
        return [pn for pn, _ in items]

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------

    @staticmethod
    def _depth(top: str, path: str) -> int:
        """Return the depth of *path* relative to *top*."""
        rel = os.path.relpath(path, top)
        if rel == '.':
            return 0
        return len(rel.split(os.sep))

    def _name_filter(self, s: str) -> bool:
        """Apply self.names / self.excludes filter (pre-expression check)."""
        base = os.path.basename(s)
        if self.excludes:
            for pat in self.excludes:
                if fnmatch.fnmatch(base, pat):
                    return False
        if '*' in self.names:
            return True
        return any(fnmatch.fnmatch(base, pat) for pat in self.names)

    def _match(self, pathname: str) -> bool:
        """Evaluate the expression tree against *pathname*."""
        if self._expr_tree is None:
            return True
        self._path = pathname
        try:
            self._st = os.stat(pathname)
        except OSError:
            return False
        if self.DEBUG:
            logging.debug("evaluating '%s'", pathname)
        return bool(self._expr_tree(self))

    def _sortcmp(self, x: tuple, y: tuple) -> int:
        for order in self._sort_by:
            if order == SORT_PATHNAME:
                r = _cmp(x[0], y[0])
            elif order == SORT_NAME:
                r = _cmp(os.path.basename(x[0]), os.path.basename(y[0]))
            elif order == SORT_EXT:
                r = _cmp(os.path.splitext(x[0])[1], os.path.splitext(y[0])[1])
            elif order == SORT_SIZE:
                r = _cmp(x[1].st_size, y[1].st_size)
            elif order == SORT_ATIME:
                r = _cmp(x[1].st_atime, y[1].st_atime)
            elif order == SORT_MTIME:
                r = _cmp(x[1].st_mtime, y[1].st_mtime)
            elif order == SORT_CTIME:
                r = _cmp(x[1].st_ctime, y[1].st_ctime)
            else:
                r = 0
            if r != 0:
                return r
        return 0

    # ------------------------------------------------------------------
    # Predicate implementations  (called by _Predicate nodes)
    # ------------------------------------------------------------------

    def _name(self, pat: str) -> bool:
        return fnmatch.fnmatchcase(os.path.basename(self._path), pat)

    def _iname(self, pat: str) -> bool:
        return fnmatch.fnmatch(os.path.basename(self._path), pat)

    def _wholename(self, pat: str) -> bool:
        return fnmatch.fnmatchcase(self._path, pat)

    def _iwholename(self, pat: str) -> bool:
        return fnmatch.fnmatch(self._path, pat)

    def _regex(self, pat: str) -> bool:
        return bool(re.search(pat, self._path))

    def _iregex(self, pat: str) -> bool:
        return bool(re.search(pat, self._path, re.IGNORECASE))

    def _type(self, code: str) -> bool:
        if code == 'f':
            return os.path.isfile(self._path)
        if code == 'd':
            return os.path.isdir(self._path)
        if code == 'l':
            return os.path.islink(self._path)
        return False

    def _empty(self) -> bool:
        if os.path.isdir(self._path):
            return not os.listdir(self._path)
        return self._st.st_size == 0

    def _executable(self) -> bool:
        return os.access(self._path, os.X_OK)

    def _readable(self) -> bool:
        return os.access(self._path, os.R_OK)

    def _writable(self) -> bool:
        return os.access(self._path, os.W_OK)

    def _size(self, op: str, n: float, m: str) -> bool:
        S = self._st.st_size
        F = {'': 1, 'b': 512, 'c': 1, 'w': 2,
             'k': 1 << 10, 'm': 1 << 20, 'g': 1 << 30, 't': 1 << 40}.get(m, 1)
        return _op(op)(S, int(n * F))

    def _date(self, typ: str, op: str, dd: int, mm: int, yy: int) -> bool:
        ts   = _stat_time(self._st, typ)
        T    = time.localtime(ts)
        T1   = datetime.date(T.tm_year, T.tm_mon, T.tm_mday)
        if 0 <= yy <= 70:
            yy += 2000
        elif 70 < yy < 100:
            yy += 1900
        T2 = datetime.date(yy, mm, dd)
        if self.DEBUG:
            logging.debug('-%sdate %s on %s and %s', typ, op, T1, T2)
        return _op(op)(T1, T2)

    def _hour(self, typ: str, op: str, hh: int, mm: int) -> bool:
        ts = _stat_time(self._st, typ)
        T  = time.localtime(ts)
        T1 = datetime.time(T.tm_hour, T.tm_min)
        T2 = datetime.time(hh, mm)
        return _op(op)(T1, T2)

    def _time(self, typ: str, op: str, n: float) -> bool:
        # Compare elapsed 24-h intervals using raw epoch seconds.
        # st_atime in particular can be refreshed by os.stat() itself on
        # some Linux mount options, so we must use the timestamp captured
        # at Search construction time (self._now_epoch) as the reference.
        ts    = _stat_time(self._st, typ)
        # Truncate both ends to midnight (GNU find -time semantics)
        base  = self._now_epoch - (self._now_epoch % 86400)
        t_day = ts - (ts % 86400)
        elapsed_days = (base - t_day) / 86400
        return _op(op)(elapsed_days, n)

    def _time_min(self, typ: str, op: str, mm: float) -> bool:
        # Use raw epoch difference to avoid any datetime conversion artefact
        # and the atime-refresh race condition described above.
        ts      = _stat_time(self._st, typ)
        elapsed = (self._now_epoch - ts) / 60.0   # minutes ago
        return _op(op)(elapsed, mm)

    def _newer(self, typ: str, name: str) -> bool:
        try:
            st2 = os.stat(name)
        except OSError:
            return False
        return _stat_time(self._st, typ) > _stat_time(st2, typ)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

_HELP = r"""
pyfind - search for files in a directory tree (GNU find-compatible subset)

Syntax:
    pyfind [root] [expression]

'root'       Path to start the search from (default: current directory)

'expression' One or more switches, combined with logical operators:

  Operators (in increasing binding strength):
    -or  | -o          Logical OR  (lower precedence)
    -and | -a          Logical AND (higher precedence, also implicit)
    -not | -!          Logical NOT
    ( expr )           Grouping  -- spaces around parentheses are optional
                       when used as a library; from bash use \( and \)
                       since bash treats bare parentheses as special syntax
                       (identical behaviour to GNU find)

  Predicates:
    -name  <glob>      Match filename, case-sensitive
    -iname <glob>      Match filename, case-insensitive

    -path  <glob>      Match full path, case-sensitive
    -ipath <glob>      Match full path, case-insensitive
    -wholename <glob>  Alias for -path
    -iwholename <glob> Alias for -ipath

    -regex  <re>       Full-path regex, case-sensitive
    -iregex <re>       Full-path regex, case-insensitive

    -type  <d|f|l>     d=directory  f=regular file  l=symlink

    -size  [+=-]<n>[bcwkmgt]
                       b=512-byte blocks  c=bytes (default)  w=16-bit words
                       k=KiB  m=MiB  g=GiB  t=TiB
                       + means greater than, - means less than, = means exactly

    -atime | -ctime | -mtime [+=-]<n>
                       Access/change/modify time, in 24-h intervals ago

    -amin  | -cmin  | -mmin  [+=-]<n>
                       Access/change/modify time, in minutes ago

    -anewer | -cnewer | -mnewer <file>
                       Select objects newer than <file>

    -adate | -cdate | -mdate [+=-] dd/mm/yy[yy]
                       Access/change/modify date  (Pythonic extension)

    -ahour | -chour | -mhour [+=-] hh:mm
                       Access/change/modify hour  (Pythonic extension)

    -mindepth <n>      Ignore objects at depth less than <n>
    -maxdepth <n>      Do not descend past depth <n>

    -empty             True if file is empty or directory is empty
    -executable        True if file is executable by current user
    -readable          True if file is readable by current user
    -writable          True if file is writable by current user

    -daystart          Measure times from the start of today (not right now)

    -true | -false     Always true / always false

Examples:
    pyfind . -name "*.py"
    pyfind /tmp -size +1m -mmin -30
    pyfind . -type f -not -name "*.pyc"
    pyfind . -size +1m -a -cmin -25 -a \( -name "*.py" -o -name "*.pyc" \)
    pyfind /var/log -mtime +7 -name "*.log"
    pyfind . -maxdepth 2 -type d -empty

  Note: in bash, parentheses must be escaped with backslash (\( and \))
  or quoted ('(' and ')') -- exactly as with GNU find.
  Spaces around parentheses are no longer required by pyfind itself.
"""


def main() -> None:
    args = sys.argv[1:]

    if not args or args[0] in ('-h', '--help'):
        print(_HELP)
        sys.exit(0)

    # First argument is root if it looks like a path
    if args and not args[0].startswith('-') and args[0] not in ('(', '!'):
        root = args[0]
        expr_parts = args[1:]
    else:
        root = '.'
        expr_parts = args

    if not os.path.isdir(root):
        print(f"pyfind: '{root}': No such directory", file=sys.stderr)
        sys.exit(1)

    expr = ' '.join(expr_parts)

    try:
        search = Search(root, expr if expr.strip() else None)
    except SyntaxError as e:
        print(f"pyfind: expression error: {e}", file=sys.stderr)
        sys.exit(1)

    try:
        for path in search.find():
            print(path)
    except KeyboardInterrupt:
        pass


if __name__ == '__main__':
    main()
