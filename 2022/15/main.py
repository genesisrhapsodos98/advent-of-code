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

class Sensor:
    def __init__(self, line):
        parts = line.split()
        self.position = tuple(map(int, (parts[2][2:-1], parts[3][2:-1])))
        self.beacon = tuple(map(int, (parts[8][2:-1], parts[9][2:])))
        self.scan_dist = sum(abs(p - b) for p, b in zip(self.position, self.beacon))

def parse_input(s):
    lines = s.splitlines()
    sensors = list(map(Sensor, lines))
    return sensors

def part1(s):
    sensors = parse_input(s)
    TARGET_Y = 2_000_000

    beacons_in_row = len(set(s.beacon[0] for s in sensors if s.beacon[1] == TARGET_Y))

    visible_ranges = []
    for s in sensors:
        half_width = s.scan_dist - abs(s.position[1] - TARGET_Y)
        if half_width < 0:
            continue

        visible_ranges.append((s.position[0] - half_width, s.position[0] + half_width))

    visible_ranges.sort()

    compact = []
    low_x, high_x = visible_ranges[0]
    for n_low_x, n_high_x in visible_ranges[1:]:
        if n_low_x - 1 <= high_x:
            high_x = max(high_x, n_high_x)
        else:
            compact.append((low_x, high_x))
            low_x, high_x = n_low_x, n_high_x
    compact.append((low_x, high_x))
    answer = sum(high-low+1 for low, high in compact) - beacons_in_row

    lib.aoc.give_answer_current(1, answer)

def part2(s):
    sensors = parse_input(s)
    MIN_COORD = 0
    MAX_COORD = 4_000_000
    def tuning_frequency(x, y):
        return x * 4_000_000 + y
    for y in range(MIN_COORD, MAX_COORD + 1):
        ranges = []
        for s in sensors:
            half_width = s.scan_dist - abs(s.position[1] - y)
            if half_width < 0:
                continue

            ranges.append((s.position[0] - half_width,
                           s.position[0] + half_width))

        ranges.sort()

        compact = []
        low_x, high_x = ranges[0]
        for n_low_x, n_high_x in ranges[1:]:
            if n_low_x - 1 <= high_x:
                high_x = max(high_x, n_high_x)
            else:
                compact.append((low_x, high_x))
                low_x, high_x = n_low_x, n_high_x
        compact.append((low_x, high_x))

        if len(compact) != 1:
            assert (len(compact) == 2)
            (a, b), (c, d) = compact
            assert (b + 2 == c)
            x = b + 1
            answer = tuning_frequency(x, y)
            break
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
