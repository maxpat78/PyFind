"""
pyfind.py 0.13

This module provides a simple tool to search a directory tree for files
matching some criteria, in a way similar to GNU find.

However, not all find switches are implemented, most noticeably it lacks
sym/hard links stuff.

A sample:
	from pyfind import Search
	
	# Finds all files greater than 1 MiB, created in the last 25 minutes,
	# whose name ends in '.py' or '.pyc'
	for found in Search('.', '-size +1m -a -cmin -25 -a ( -name *.py -or -name *.pyc )').find():
		print (found)
		
Also, it provides some extension switches: -Xdate and -Xhour, to test date
and times in a more user-friendly way (and better than -xnewerXY).

TODO:
- check -a -anewer regex for strange duplication?
- -xtime 0 means "less than 24-hrs ago"
- -used?
- -newerXY?
- -prune?
- -depth? --> when calculating depth, top != curdir != worked dir
              (i.e. top=..\..\somedir, cur=somedir, wd=..\..\anotherdir)
"""

import sys, datetime, fnmatch, os, operator, re, shlex, time, functools
import logging
import argparse


# Sort types
NO_SORT        = -1
SORT_PATHNAME  = 0
SORT_NAME      = 1
SORT_EXT       = 2
SORT_SIZE      = 3
SORT_ATIME     = 4
SORT_CTIME     = 5
SORT_MTIME     = 6


# List of Tuples (switch regex, args number, arg regex, arg replacement regex)

Evaluable = [
# +x: means greater than x
# -x: means less than x
# =x: means equal to x
# x : alias for =x

# -size +0.5m, -size 1033 etc.
# b means 512 bytes blocks; c means bytes (implicit); w means 16-bit words; k,m,g,t --> KiB, MiB, GiB, TiB
('-size', 1, '([+=-]*)([0-9.]+)([bcwkmgt]*)', 'p._size("\\1",\\2,"\\3")'),

# -adate +1.9.2012, -mdate -01/01/12 etc. A Pythonic extension. (dd/mm/00 ... dd/mm/70 --> 2000...2070)
('-([acm])date', 1, '([+=-]*)([0-9]{1,2})[./]([0-9]{1,2})[./]([0-9]{2,4})', 'p._date("\\1","\\2",\\3,\\4,\\5)'),

# -chour +13:10, -mhour -6.00 etc. A Pythonic extension.
('-([acm])hour', 1, '([+=-]*)([0-9]{1,2})[:.]([0-9]{1,2})', 'p._hour("\\1","\\2",\\3,\\4)'),

# -ctime +2, -mtime -6.5 etc. Times in 24-hours intervals ago (Unix style)
('-([acm])time', 1, '([+=-]*)([0-9]+[.0-9]*)', 'p._time("\\1","\\2",\\3)'),

# -cmin +2, -mmin -6 etc. Times in minutes ago (Unix style)
('-([acm])min', 1, '([+=-]*)([0-9.]+)', 'p._time_min("\\1","\\2",\\3)'),

# -mnewer file.ext, etc.
('-([acm])newer', 1, '(.+)', 'p._newer("\\1","\\2")'),

# -mindepth/-maxdepth (special case)
('-(min|max){1}depth', 1, '(\d+)', 'p.\\1depth=\\2'),

# replaces with Python operators
('-a(nd)*', 0, '', 'and'),
('-o(r)*', 0, '', 'or'),
('-not', 0, '', 'not'),
('-true', 0, '', 'True'),
('-false', 0, '', 'False'),

#~ ('-daystart', 0, '', 'p.NOW=datetime.datetime.now().replace(minute=0,second=0,microsecond=0)'),

# -name/-iname pattern
('-([i]?)name', 1, '(.+)', 'p._\\1name(r"\\2")'),
# -path/-ipath/-wholename/-iwholename pattern
('-([i]?)(wholename|path)', 1, '(.+)', 'p._\\1wholename(r"\\3")'),
# -regex/-iregex expression
('-([i]?)regex', 1, '(.+)', 'p._\\1regex(r"\\2")'),
# -type d=dir, f=file
('-type', 1, '([df])', 'p._type("\\1")'),
]



def cmp(a, b):
	"Provides old Python 2 cmp function"
	return (a > b) - (a < b) 



class Search:
	def __init__(p, root='.', expr=None):
		p.DEBUG    = False   # wether to print debug infos
		p.dirs     = [root]  # list of dirs to search (default: current dir)
		p.names    = ['*']   # list of filenames to search for, wildcards allowed (default: all)
		p.excludes = None    # list of filenames to exclude (default: none)
		p.mindepth = -1      # min recursion depth from initial position
		p.maxdepth = -1      # max recursion depth from initial position
		p.eval     = None    # GNU find-style expression
		p.NOW      = datetime.datetime.now() # search start time

		p.eval = []
		if p.DEBUG: logging.debug('Splitted expr: %s', shlex.split(expr))
		args = iter(shlex.split(expr))
		for switch in args:
			ok = 0
			for e in Evaluable:
				if re.match(e[0], switch):
					ok = 1
					arg = ''
					if e[1]:
						arg = next(args)
						if not re.match(e[2], arg):
							raise SyntaxError("Wrong argument '%s' for switch '%s'!" % (arg, switch))
					if p.DEBUG: logging.debug('switch="%s" arg="%s"', switch, arg)
					#~ print 'groups=', re.match(' '.join((e[0],e[2])), ' '.join((switch,arg))).groups()
					p.eval += [re.sub(''.join((e[0],e[2])), e[3], ''.join((switch,arg)))]
			if switch in ('(',')'):
				ok = 1
				p.eval += [switch]
			booleans = ('and','or','not','true','false')
			if len(p.eval) > 1 and \
			p.eval[-1] not in booleans and p.eval[-2] not in booleans and \
			p.eval[-2] != '(' and p.eval[-1] != ')' :
				if p.DEBUG: logging.debug("implicit: %s *AND* %s", p.eval[-2], p.eval[-1])
				p.eval.insert(-1, "and")
			if not ok:
				if switch == '-daystart':
					p.NOW = p.NOW.replace(hour=0,minute=0,second=0,microsecond=0)
				else:
					raise SyntaxError("Wrong switch '%s'!" % switch)
		if p.DEBUG: logging.debug("Parsed expr: %s", p.eval)
		for subst in ('p.mindepth', 'p.maxdepth'):
			for item in p.eval:
				if subst in item:
					exec(item) # immediately alters the instance and deletes
					del p.eval[p.eval.index(item)]
		if p.DEBUG: logging.debug("Subst expr: %s", p.eval)
		p.eval = ' '.join(p.eval)

	def find(p, with_stat=False):
		"""Traverses the dir tree and yields every matching pathname
		(or a tuple (pathname, stat) if with_stat is True)"""
		def depth(top, path):
			return len(path.split('\\')) - len(top.split('\\'))
		for top in p.dirs:
			for root, dirs, files in os.walk(top):
				# However, os.walk() pre-scans the full tree...
				if p.maxdepth > -1 and depth(top, root) > p.maxdepth:
					if p.DEBUG: logging.debug("Skipping '%s', depth=%d>%d", root, depth(top, root), p.maxdepth)
					continue
				if p.mindepth > -1 and depth(top, root) < p.mindepth:
					if p.DEBUG: logging.debug("Skipping '%s', depth=%d<%d", root, depth(top, root), p.mindepth)
					continue
				for item in files:
					pn = os.path.join(root, item)
					if p.__name(pn) and p._reliqua(pn):
						if not with_stat:
							yield pn
						else:
							yield pn, os.stat(pn)
				for item in dirs:
					pn = os.path.join(root, item)
					if p.__name(pn) and p._reliqua(pn):
						if not with_stat:
							yield pn
						else:
							yield pn, os.stat(pn)

	def findall(p, with_stat=False):
		"""Traverses the dir tree and returns every matching pathname
		(or a dictionary {pathname: stat} for all matching pathnames"""
		found = dict( [o for o in p.find(1)] )
		if with_stat:
			return found
		else:
			return found.keys()

	def _sortcmp(p, x, y):
		"Sorts findall() results according to one or more criteria"
		r = 0
		for order in p.sort_by:
			if order == SORT_PATHNAME:
				r = cmp(x[0], y[0])
			elif order == SORT_NAME:
				r = cmp(os.path.basename(x[0]), os.path.basename(y[0]))
			elif order == SORT_EXT:
				r = cmp(os.path.splitext(os.path.basename(x[0]))[1], os.path.splitext(os.path.basename(y[0]))[1])
			elif order == SORT_SIZE: # from smallest
				r = cmp(x[1].st_size, y[1].st_size)
			elif order == SORT_ATIME: # from oldest
				r = cmp(x[1].st_atime, y[1].st_atime)
			elif order == SORT_MTIME:
				r = cmp(x[1].st_mtime, y[1].st_mtime)
			elif order == SORT_CTIME:
				r = cmp(x[1].st_ctime, y[1].st_ctime)
			if r == 0:
				continue
			else:
				break
		return r

	def sortall(p, result, sort_by, with_stat=False):
		"Sorts the findall() results and returns a list of tuples (pathname, stat)"
		if type(result) != type({}):
			raise SyntaxError("You can sort only a dictionary {pathname: stat} returned by findall()!")
		found = result.items()
		p.sort_by = sort_by
		return sorted(found, key=functools.cmp_to_key(p._sortcmp))

	def _op(p, op):
		try:
			OP = [operator.eq,operator.gt,operator.lt][['=','+','-'].index(op)]
		except ValueError:
			OP = operator.eq # None, or other
		return OP

	def __name(p, s):
		if p.excludes:
			for pat in p.excludes:
				if fnmatch.fnmatch(s, pat):
					return 0
		if '*' in p.names:
			return 1
		for pat in p.names:
			if fnmatch.fnmatch(s, pat):
				return 1
		return 0

	def _name(p, s):
		return fnmatch.fnmatchcase(os.path.basename(p.PathName), s)

	def _iname(p, s):
		return fnmatch.fnmatch(os.path.basename(p.PathName), s)

	def _wholename(p, s):
		return fnmatch.fnmatchcase(p.PathName, s)

	def _iwholename(p, s):
		return fnmatch.fnmatch(p.PathName, s)

	def _regex(p, s):
		return re.match(s, p.PathName)

	def _iregex(p, s):
		return re.match(s, p.PathName, re.I)

	def _type(p, code):
		if code == 'f':
			return os.path.isfile(p.PathName)
		elif code == 'd':
			return os.path.isdir(p.PathName)

	def _reliqua(p, s):
		if not p.eval:
			return 1
		p.PathName = s # current pathname to test
		p.ST = os.stat(s) # its stats
		if p.DEBUG: logging.debug("evaluating '%s' for '%s', STAT='%s'", p.eval, s, p.ST)
		try:
			res = eval(p.eval)
		except SyntaxError:
			print("'%s': bad expression! Did you forget -and/-or operators on command line, perhaps?"%p.eval)
			sys.exit(1)
		return res

	def _size(p, op, n, m):
		S = p.ST.st_size
		OP = p._op(op)
		F = [1,512,1,2,1<<10,1<<20,1<<30,1<<40][['','b','c','w','k','m','g','t'].index(m)]
		return OP(S, n*F)

	def _date(p, typ, op, dd, mm, yy):
		T = time.localtime(p.ST[-1-['c','m','a'].index(typ)])
		OP = p._op(op)
		T1 = datetime.date(T.tm_year, T.tm_mon, T.tm_mday)
		if 0 <= yy <= 70: # Handles 2-digits years
			yy += 2000
		elif 70 < yy < 99:
			yy += 1900
		T2 = datetime.date(yy, mm, dd)
		if p.DEBUG: logging.debug("-%cdate %s on %s and %s)",typ,OP,T1,T2)
		return OP(T1, T2)

	def _time(p, typ, op, n):
		T = time.localtime(p.ST[-1-['c','m','a'].index(typ)])
		OP = p._op(op)
		T1 = datetime.datetime(T.tm_year, T.tm_mon, T.tm_mday, T.tm_hour, T.tm_min, T.tm_sec)
		T2 = datetime.timedelta(hours=24*n)
		if p.DEBUG: logging.debug("-%ctime %s on (%s - %s = %s) and %s = %s",typ,OP,p.NOW,T1,p.NOW-T1,T2,OP(p.NOW-T1, T2))
		return OP(p.NOW-T1, T2)

	def _hour(p, typ, op, hh, mm):
		T = time.localtime(p.ST[-1-['c','m','a'].index(typ)])
		OP = p._op(op)
		T1 = datetime.time(T.tm_hour, T.tm_min, 0)
		T2 = datetime.time(hh, mm, 0)
		if p.DEBUG: logging.debug("-%chour %s on %s and %s)",typ,OP,T1,T2)
		return OP(T1, T2)

	def _time_min(p, typ, op, mm):
		T = time.localtime(p.ST[-1-['c','m','a'].index(typ)])
		OP = p._op(op)
		T1 = datetime.datetime(T.tm_year, T.tm_mon, T.tm_mday, T.tm_hour, T.tm_min, T.tm_sec)
		T2 = datetime.timedelta(minutes=mm)
		if p.DEBUG: logging.debug("-%cmin %s on (%s - %s = %s) and %s = %s",typ,OP,p.NOW,T1,p.NOW-T1,T2,OP(p.NOW-T1, T2))
		return OP(p.NOW-T1, T2)

	def _newer(p, typ, name):
		ST1 = p.ST[-1-['c','m','a'].index(typ)]
		ST2 = os.stat(name)[-1-['c','m','a'].index(typ)]
		return ST1 > ST2


if __name__ == '__main__':
	#~ logging.basicConfig(level=logging.DEBUG, filename='pyfind_debug.log', filemode='w')
	if len(sys.argv) == 1:
		root, expr = '.', ''
	elif len(sys.argv) == 2:
		if sys.argv[1] == '-h':
			print("""Searches for files and directories in a way similar to GNU find.

Syntax: pyfind [root] [expression]

'root' is the path to start the search from

'expression' is one or more switches to refine search (please note that '+' means 'greater than', '-' means 'less than' and '=' means 'equal to' (and is implicit):

 -size [+-=] <n>[bcwkmgt]
 selects files with a given size ('b' is a 512 bytes sector, 'c' is character and is implicit and equivalent to byte, 'w' means 16-bit word, 'k' is kibibyte, 'm' is mebibyte, 'g' is gibibyte and 't' is tebibyte)

 -adate | -cdate | -mdate [+-=] dd/mm/yy
 selects objects with a given access, creation or modification date
 
 -ahour | -chour | -mhour [+-=] <hh:mm> or <hh.mm>
 selects objects with a given access, creation or modification hour and minute

 -atime | -ctime | -mtime [+-=] <nn>
 selects objects with a given access, creation or modification time, expressed as 24-hour intervals (Unix-like)
 
 -amin | -cmin | -mmin  [+-=] <mm>
 selects objects with a given access, creation or modification time, expressed in minutes (Unix-like)
 
 -anewer | -cnewer | -mnewer <file>
 selects objects newer than a given file
 
 -mindepth | -maxdepth <n>
 selects objects whose depth is at least/most <n> in respect of 'root'
 
 -name | -iname <glob>
 selects all file names matching a <glob> expression, in a case sensitive or insensitive manner

 -path | -ipath <glob>
 -wholename | -iwholename <glob>
 selects all path names matching a <glob> expression, in a case sensitive or insensitive manner

 -regex | -iregex <regex>
 selects all path names matching a given regular expression, in a case sensitive or insensitive manner
 
 -daystart
 all time-relative computations are from the start of this day (and not from this moment)
 
 -type <d> | <f>
 selects objects whose type is directory or file

Moreover, switches can be combined with -and, -or, -not, -true and -false operators.

Example:
pyfind . -size +1m -a -cmin -25 -a ( -name *.py -or -name *.pyc )
searches for all .py and .pyc files >1M created in the last 25 minutes (note
the space after and before the round brackets: it is mandatory!)""")
			sys.exit(1)
		root, expr = sys.argv[1], ''
	else:
		root, expr = sys.argv[1], ' '.join(sys.argv[2:])
		
	if not os.path.isdir(root):
		print("pyfind error: first argument, if provided, must be a directory!")
		sys.exit(1)

	for o in Search(root, expr).findall():
		print(o)
