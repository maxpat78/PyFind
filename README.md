PyFind
======

This module provides a simple tool to search a directory tree for files
matching some criteria, in a way similar to GNU find.

It works both from command line and as a module.

A sample:
```

	from pyfind import Search
	
	# Finds all files greater than 1 MiB, created in the last 25 minutes,
	# whose name ends in '.py'
	for found in Find('.', '-size +1m -a -cmin -25 -a -name *.py').find():
		print found
```
		
Also, it provides some extension switches: -Xdate and -Xhour, to test date
and times in a more user-friendly way (and better than -xnewerXY).


The code is given to the Public Domain.