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
    instructions = []
    for line in lines:
        direction = line[0]
        amount = int(line[1:])
        instructions.append((direction, amount))
    return instructions

def part1(s):
    instructions = parse_input(s)
    current = 50
    answer = 0
    for (d, a) in instructions:
        if d == 'L':
            current -= a
        else:
            current += a
        current = current % 100
        if current == 0:
            answer += 1
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
    _ = parse_input(s)
    answer = 0
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
