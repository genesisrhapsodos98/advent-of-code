from itertools import product

import lib.aoc
import lib.graph
import lib.grid


def parse_input(s):
    groups = s.split('\n\n')
    grids = []
    for group in groups:
        grid = lib.grid.FixedGrid.parse(group)
        grids.append(grid)
    return grids


def fit(lock, key):
    result = True
    for i in lock.x_range:
        lock_height = len([x for x in lock.col(i) if x == '#'])
        key_height = len([x for x in key.col(i) if x == '#'])
        if lock_height + key_height > lock.height:
            result = False
            break
    return result


def part1(s):
    grids = parse_input(s)
    locks = [grid for grid in grids if '#' in grid.row(0)]
    keys = [grid for grid in grids if '.' in grid.row(0)]
    answer = 0
    for lock, key in product(locks, keys):
        if fit(lock, key):
            answer += 1
    lib.aoc.give_answer_current(1, answer)


def part2(s):
    print('There is no part two for Christmas!')


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
