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

def parse_snafu(num):
    total = 0
    for c in num:
        total = total * 5 + ('=-012'.index(c) - 2)

    return total

def to_snafu(num):
    output = ''

    while num != 0:
        # Offsetting the number at this place makes conversion simple
        num, place = divmod(num + 2, 5)
        output += '=-012'[place]

    return output[::-1]

def part1(s):
    answer = to_snafu(sum(map(parse_snafu, s.splitlines())))
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    print('There is no part two for Christmas!')

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
