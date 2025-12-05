import collections
import functools
import itertools
import json
import math
import parse
import re2 as re
import sympy # sympy.parse_expr, sympy.solve, sympy.Eq
import sys # sys.setrecursionlimit(1000000)
import z3 # x = z3.Int('x'); x < 0; (x-1) >= 0
# z3.If(x >= 0, x, -x); z3.And(); z3.Or(); z3.Not()
# s = z3.Solver(); solver.add(constraint); s.check(); s.model()[x].as_long()
# o = z3.Optimize(); o.minimize(x); o.check(); o.model()[x].as_long()

import lib.algorithms
import lib.aoc
import lib.cyk
import lib.graph
from lib.graphics import *
import lib.grid
import lib.hex_coord
import lib.lazy_dict
import lib.math
import lib.ocr
import lib.parsing

def parse_input(s):
    monkeys = {}
    for line in s.splitlines():
        if not line:
            continue
        name, job = line.split(': ')
        parts = job.split()
        if len(parts) == 1:
            monkeys[name] = int(parts[0])
        else:
            monkeys[name] = parts
    return monkeys

def part1(s):
    monkeys = parse_input(s)
    sys.setrecursionlimit(20000)

    @functools.cache
    def evaluate(name):
        val = monkeys[name]
        if isinstance(val, int):
            return val
        
        lhs, op, rhs = val
        v1 = evaluate(lhs)
        v2 = evaluate(rhs)
        
        if op == '+': return v1 + v2
        if op == '-': return v1 - v2
        if op == '*': return v1 * v2
        if op == '/': return v1 // v2

    answer = evaluate('root')
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
    monkeys = parse_input(s)
    # lib.aoc.give_answer_current(2, answer)
INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
