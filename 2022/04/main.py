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
    pairs = [
        [tuple(map(int, pair.split('-'))) for pair in line.split(',')]
        for line in s.splitlines()
    ]
    return pairs

def part1(s):
    pairs = parse_input(s)
    answer = 0
    for pair in pairs:
        [l, r] = pair
        sl, el = l
        sr, er = r
        if (sl <= sr and el >= er) or (sr <= sl and er >= el):
            answer += 1
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
    _ = parse_input(s)
    answer = 0
    # lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
