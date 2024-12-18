import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid
from lib.graph import all_reachable


def part1(s):
    grid = lib.grid.FixedGrid.parse(s)
    start = grid.find('S')
    grid[start] = '.'

    positions = [start]
    for i in range(64):
        next_positions = set()
        for p in positions:
            next_positions.update(grid.neighbors(*p))

        positions = [p for p in next_positions if grid[p] != '#']

    answer = len(positions)

    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
    answer = 0
    # lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
