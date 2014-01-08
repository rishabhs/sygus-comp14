#Embedded file name: src/api/python/z3test.py
import z3, doctest
r = doctest.testmod(z3)
if r.failed != 0:
    exit(1)
