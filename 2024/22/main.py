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
    lines = s.splitlines()
    numbers = list(map(int, lines))
    return numbers

def mix(num, val):
    return val ^ num

def prune(num):
    return num % 16777216

def randomize(seed):
    result = prune(mix(seed, seed * 64))
    result = prune(mix(result, result // 32))
    result = prune(mix(result, result * 2048))
    return result

def part1(s):
    numbers = parse_input(s)
    answer = 0

    for num in numbers:
        final = num
        for _ in range(2000):
            final = randomize(final)
        answer += final
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
    _ = parse_input(s)
    answer = 0
    # lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
