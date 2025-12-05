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
    [(2, 0), (3, 0), (4, 0), (5, 0)], # Horizontal Line
    [(3, 0), (2, 1), (3, 1), (4, 1), (3, 2)], # Plus
    [(2, 0), (3, 0), (4, 0), (4, 1), (4, 2)], # L
    [(2, 0), (2, 1), (2, 2), (2, 3)], # Vertical Bar
    [(2, 0), (2, 1), (3, 0), (3, 1)], # Square
]

def solve(s, CYCLE_COUNT):
    TOWER_WIDTH = 7

    tower = {(x, 0) for x in range(TOWER_WIDTH)}
    tower_height = 0
    column_heights = [0] * TOWER_WIDTH

    cycle_idx = 0
    jet_idx = 0

    history = collections.defaultdict(list)

    while cycle_idx < CYCLE_COUNT:
        current_cycle = cycle_idx
        cycle_idx += 1

        rock_idx = current_cycle % len(ROCKS)
        rock = ROCKS[rock_idx]
        y_off = tower_height + 4
        rock = [(x, y+y_off) for x, y in rock]

        cycle_key = (rock_idx, jet_idx)

        move_x, move_y = 0, 0

        # Make it rain!
        while True:
            jet = -1 if s[jet_idx] == '<' else 1
            jet_idx = (jet_idx + 1) % len(s)

            test_rock = [(x+jet, y) for x, y in rock]
            if any(x < 0 or x >= TOWER_WIDTH for x, y in test_rock):
                test_rock = rock
            elif any(c in tower for c in test_rock):
                test_rock = rock
            else:
                move_x += jet

            rock = test_rock
            test_rock = [(x, y-1) for x,y in rock]
            if any(c in tower for c in test_rock):
                # It settled
                tower.update(rock)
                tower_height = max(tower_height, max(y for x,y in rock))
                for x, y in rock:
                    column_heights[x] = max(column_heights[x], y)

                if history is None:
                    # We must be wrapping up at this point
                    break

                top_characteristic = tuple(y-tower_height
                                           for y in column_heights)

                key = (cycle_key, move_x, move_y, top_characteristic)

                cycle_history = history[key]

                if len(cycle_history) > 1:
                    last_y_diff = cycle_history[-1][0] - cycle_history[-2][0]
                    curr_y_diff = tower_height - cycle_history[-1][0]

                    if last_y_diff == curr_y_diff:
                        cycle_diff = current_cycle - cycle_history[-1][1]

                        remaining_cycles = CYCLE_COUNT - current_cycle - 1

                        supercycles = remaining_cycles // cycle_diff
                        skipped_cycles = supercycles * cycle_diff

                        height_mod = supercycles * curr_y_diff

                        tower = {(x, y+height_mod) for x, y in tower}
                        tower_height += height_mod

                        cycle_idx += skipped_cycles

                        # We jumped ahead once, no need to do it again!
                        history = None
                        break

                cycle_history.append((tower_height, current_cycle))
                break

            move_y -= 1
            rock = test_rock

    return tower_height

def part1(s):
    jets = parse_input(s)
    answer = solve(jets, 2022)

    lib.aoc.give_answer_current(1, answer)

def part2(s):
    jets = parse_input(s)
    answer = solve(jets, 1_000_000_000_000)

    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
