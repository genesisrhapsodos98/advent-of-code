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
    grid = lib.grid.FixedGrid.parse(s, value_fn=int)
    return grid

def get_tree_stats(grid: lib.grid.FixedGrid):
    for (x, y), self_height in grid.items():
        obscured = True
        distances = []

        for dx, dy in [(-1, 0),
                       (1, 0),
                       (0, -1),
                       (0, 1)]:
            nx, ny = x, y
            num_trees_visible = 0
            while True:
                nx, ny = nx + dx, ny + dy
                if (nx, ny) not in grid:
                    obscured = False
                    break
                num_trees_visible += 1
                if grid[nx, ny] >= self_height:
                    break  # Obscured
            distances.append(num_trees_visible)

        yield distances, obscured


def part1(s):
    grid = parse_input(s)
    tree_stats = get_tree_stats(grid)
    answer = sum(1 for _, obscured in tree_stats if not obscured)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    grid = parse_input(s)
    tree_stats = get_tree_stats(grid)
    answer = max(math.prod(distances) for distances, _ in tree_stats)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
