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
    return s.strip()

ROCKS = [
    {(0,0), (1,0), (2,0), (3,0)},
    {(1,0), (0,1), (1,1), (2,1), (1,2)},
    {(0,0), (1,0), (2,0), (2,1), (2,2)},
    {(0,0), (0,1), (0,2), (0,3)},
    {(0,0), (1,0), (0,1), (1,1)},
]

def can_move(rock, dx, dy, occupied):
    for x, y in rock:
        nx, ny = x + dx, y + dy
        if nx < 0 or nx >= 7 or ny <= 0:
            return False
        if (nx, ny) in occupied:
            return False
    return True

def part1(s):
    jets = parse_input(s)
    L = len(jets)
    jet_i = 0
    occupied = set()
    height = 0

    for rock_i in range(2022):
        shape = ROCKS[rock_i % 5]
        rock = {(x+2, y+height+4) for (x,y) in shape}

        while True:
            push = jets[jet_i]
            jet_i = (jet_i + 1) % L

            if push == '<':
                if can_move(rock, -1, 0, occupied):
                    rock = {(x-1, y) for (x,y) in rock}
            else:
                if can_move(rock, 1, 0, occupied):
                    rock = {(x+1, y) for (x,y) in rock}

            if can_move(rock, 0, -1, occupied):
                rock = {(x, y-1) for (x,y) in rock}
            else:
                for pos in rock:
                    occupied.add(pos)
                    height = max(height, pos[1])
                break

    lib.aoc.give_answer_current(1, height)

def part2(jets):
    jets = parse_input(s)
    L = len(jets)
    jet_i = 0
    occupied = set()
    height = 0
    states = {}
    top_rows = 50
    target = 1000000000000
    rock_i = 0

    while rock_i < target:
        shape = ROCKS[rock_i % 5]
        rock = {(x+2, y+height+4) for (x,y) in shape}

        while True:
            push = jets[jet_i]
            jet_i = (jet_i + 1) % L

            if push == '<':
                if can_move(rock, -1, 0, occupied):
                    rock = {(x-1, y) for (x,y) in rock}
            else:
                if can_move(rock, 1, 0, occupied):
                    rock = {(x+1, y) for (x,y) in rock}

            if can_move(rock, 0, -1, occupied):
                rock = {(x, y-1) for (x,y) in rock}
            else:
                for pos in rock:
                    occupied.add(pos)
                    height = max(height, pos[1])
                break

        key = (rock_i % 5, jet_i, frozenset((x, height-y) for (x,y) in occupied if height-y <= top_rows))
        if key in states:
            old_rock_i, old_height = states[key]
            cycle_len = rock_i - old_rock_i
            cycle_height = height - old_height
            cycles = (target - rock_i) // cycle_len
            rock_i += cycles * cycle_len
            height += cycles * cycle_height
            occupied = {(x, y + cycles*cycle_height if y > height - cycle_height else y) for (x,y) in occupied}
        else:
            states[key] = (rock_i, height)

        rock_i += 1

    lib.aoc.give_answer_current(2, height)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
