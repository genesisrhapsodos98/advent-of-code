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
    lines = s.splitlines()
    motions = [tuple(line.split()) for line in lines]
    return motions

def head_positions(motions):
    x, y = 0, 0
    yield x, y

    for d, c in motions:
        if d == 'U': dx, dy = 0, -1
        elif d == 'D': dx, dy = 0, 1
        elif d == 'L': dx, dy = -1, 0
        elif d == 'R': dx, dy = 1, 0
        else: dx, dy = 0, 0

        for _ in range(int(c)):
            x, y = x + dx, y + dy
            yield x, y

def next_segment_positions(positions):
    x, y = 0, 0
    yield x, y
    for prev_x, prev_y in positions:
        dx, dy = prev_x - x, prev_y - y

        if max(abs(dx), abs(dy)) == 2:
            if dx != 0:
                x += dx // abs(dx)
            if dy != 0:
                y += dy // abs(dy)
            yield x, y

def part1(s):
    motions = parse_input(s)
    answer = len(set(next_segment_positions(head_positions(motions))))
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    motions = parse_input(s)
    rope = head_positions(motions)
    for _ in range(9):
        rope = next_segment_positions(rope)
    answer = len(set(rope))
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
