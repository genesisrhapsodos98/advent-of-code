import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid

def part1(s):
##    nums = list(map(lambda r:r[0], parse.findall('{:d}', s)))
##    lines = s.splitlines()
##    groups = s.split('\n\n')
##    grid = lib.grid.FixedGrid.parse(s, value_fn=int)
##    grid = lib.grid.FixedGrid.parse(s,
##                                    linesplit_fn=lambda line: line.split(),
##                                    value_fn=int)
    print(f'The answer to part one is {answer}')
    if input('Submit answer? ').lower() in ('y', 'yes', '1'):
        assert(lib.aoc.give_answer_current(1, answer))

def part2(s):
    pass
##    print(f'The answer to part two is {answer}')
##    if input('Submit answer? ').lower() in ('y', 'yes', '1'):
##        assert(lib.aoc.give_answer_current(2, answer))

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
