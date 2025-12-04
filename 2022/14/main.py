import collections
import functools
import itertools
import json
import math
import parse
import re2 as re
import sympy  # sympy.parse_expr, sympy.solve, sympy.Eq
import sys  # sys.setrecursionlimit(1000000)
import z3  # x = z3.Int('x'); x < 0; (x-1) >= 0
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
    cave = set()

    for line in s.splitlines():
        parts = [tuple(map(int, p.split(',')))
                 for p in line.split(' -> ')]
        x, y = parts.pop(0)
        for x2, y2 in parts:
            if x == x2:
                dy = -1 if y2 < y else 1
                cave.update((x, y) for y in range(y, y2 + dy, dy))
                y = y2
            else:
                dx = -1 if x2 < x else 1
                cave.update((x, y) for x in range(x, x2 + dx, dx))
                x = x2

    return cave

def solve(cave, in_x, in_y):
    max_y = max(y for x,y in cave)
    initial_count = len(cave)

    def settle(x, y):
        if y > max_y: # Part 1 exit condition
            return False
        if (x, y) in cave:
            return True
        # Will short circuit if any cannot settle
        if settle(x, y+1) and settle(x-1, y+1) and settle(x+1, y+1):
            cave.add((x, y))
            return True
        return False

    settle(in_x, in_y)

    return len(cave) - initial_count

def part1(s):
    answer = solve(parse_input(s), 500, 0)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    cave = parse_input(s)

    # The sand can only go so far so we don't need an infinite floor
    floor = max(y for x,y in cave) + 2
    cave.update((x, floor) for x in range(500-floor, 500+floor+1))

    answer = solve(cave, 500, 0)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
