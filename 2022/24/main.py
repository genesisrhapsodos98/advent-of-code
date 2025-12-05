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

class Valley:
    def __init__(self, s):
        grid = lib.grid.FixedGrid.parse(s)

        self.start = min(x for x in range(grid.width)
                         if grid[x,0] == '.'), 0
        self.goal = end = min(x for x in range(grid.width)
                              if grid[x, grid.height-1] == '.'), grid.height-1

        self.walls = {c for c, v in grid.items()
                      if v == '#'}
        # Don't let the elf escape the valley!
        self.walls.add((self.start[0], -1))
        self.walls.add((self.goal[0], grid.height))

        # Precompute all the blizzard states. However, precompute them on a
        # per-axis basis as those periods are much lower than the full period.

        blizzards = [(c, v) for c, v in grid.items()
                     if v in '^v']

        self.vertical_blizzards = []
        for _ in range(grid.height-2): # Exclude wall tiles in the period!
            self.vertical_blizzards.append({c
                                            for c, v
                                            in blizzards})
            new_blizzards = []
            for (x, y), v in blizzards:
                y += 1 if v == 'v' else -1
                if y == 0:
                    y = grid.height-2
                elif y == grid.height-1:
                    y = 1
                new_blizzards.append(((x, y), v))
            blizzards = new_blizzards

        blizzards = [(c, v) for c, v in grid.items()
                     if v in '<>']

        self.horizontal_blizzards = []
        for _ in range(grid.width-2): # Exclude wall tiles in the period!
            self.horizontal_blizzards.append({c
                                              for c, v
                                              in blizzards})
            new_blizzards = []
            for (x, y), v in blizzards:
                x += 1 if v == '>' else -1
                if x == 0:
                    x = grid.width-2
                elif x == grid.width-1:
                    x = 1
                new_blizzards.append(((x, y), v))
            blizzards = new_blizzards

        self.step = 0

    def move_optimally(self, begin, target):
        states = {begin}

        while target not in states:
            self.step += 1

            blocked = set(self.walls)
            blocked |= self.vertical_blizzards[self.step % len(self.vertical_blizzards)]
            blocked |= self.horizontal_blizzards[self.step % len(self.horizontal_blizzards)]

            new_states = set()

            for x, y in states:
                for n in [(x-1, y),
                          (x+1, y),
                          (x, y-1),
                          (x, y+1)]:
                    if n in blocked:
                        continue
                    new_states.add(n)
                if (x, y) not in blocked:
                    new_states.add((x, y))

            states = new_states

def parse_input(s):
    valley = Valley(s)
    return valley

def part1(s):
    valley = parse_input(s)
    valley.move_optimally(valley.start, valley.goal)
    answer = valley.step
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    valley = parse_input(s)
    valley.move_optimally(valley.start, valley.goal)
    valley.move_optimally(valley.goal, valley.start)
    valley.move_optimally(valley.start, valley.goal)
    answer = valley.step
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
