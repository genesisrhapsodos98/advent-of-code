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
    return lib.grid.FixedGrid.parse(s)

def part1(s):
    grid = parse_input(s)
    answer = sum(
        1
        for (x, y), v in grid.items()
        if v == '@' and sum(grid[nx, ny] == '@' for nx, ny in grid.neighbors(x, y, diagonals=True)) < 4
    )
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
    _ = parse_input(s)
    answer = 0

INPUT = lib.aoc.get_current_input()
part1(INPUT)
