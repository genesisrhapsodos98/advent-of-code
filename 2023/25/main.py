import collections
import functools
import itertools
import json
import math

import networkx
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

def solve(s):
    g = networkx.Graph()

    for line in s.splitlines():
        src, dests = line.split(': ')
        for d in dests.split():
            g.add_edge(src, d, capacity=1)

    nodes = list(g)

    for idx, n1 in enumerate(nodes):
        for n2 in nodes[idx+1:]:
            num_cuts, (left, right) = networkx.minimum_cut(g, n1, n2)
            if num_cuts == 3:
                return len(left) * len(right)

def part1(s):
    answer = solve(s)

    lib.aoc.give_answer(2023, 25, 1, answer)


def part2(s):
    print('There is no part two for Christmas!')

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
