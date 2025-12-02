import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid
from lib.graphics import *

def parse_input(s):
    pairs = s.split(',')
    ranges = [tuple(map(int, pair.split('-'))) for pair in pairs]
    return ranges

def repeated_twice_pattern(s):
    n = len(s)
    if n % 2 != 0:
        return None

    half = n // 2
    unit = s[:half]

    if unit * 2 == s:
        return unit

    return None

def part1(s):
    ranges = parse_input(s)
    answer = 0
    for (start, end) in ranges:
        for n in range(start, end + 1):
            p = repeated_twice_pattern(str(n))
            if p is not None:
                answer += n
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
    _ = parse_input(s)
    answer = 0
    # lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
