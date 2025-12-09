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
    instructions = [line.split() for line in s.splitlines()]
    return instructions

def register_per_cycle(instructions):
    value_per_cycle = []

    x = 1

    for instruction in instructions:
        op = instruction[0]
        if op == 'noop':
            value_per_cycle += [x]
        elif op == 'addx':
            value_per_cycle += [x, x]
            x += int(instruction[1])
        else:
            assert(False)

    return value_per_cycle

def part1(s):
    instructions = parse_input(s)
    value_per_cycle = register_per_cycle(instructions)
    answer = sum(cycle * value_per_cycle[cycle - 1] for cycle, _ in enumerate(value_per_cycle) if (cycle - 20) % 40 == 0)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    instructions = parse_input(s)
    value_per_cycle = register_per_cycle(instructions)
    lit_pixels = {
        (cycle % 40, cycle // 40)
        for cycle, pos in enumerate(value_per_cycle)
        if cycle % 40 in (pos - 1, pos, pos + 1)
    }
    answer = lib.ocr.parse_coord_set(lit_pixels)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
