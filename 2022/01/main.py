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
    groups = s.split('\n\n')

    elves = [[int(n) for n in group.splitlines()] for group in groups]
    return elves

def part1(s):
    elves = parse_input(s)
    answer = max([sum(elf) for elf in elves])
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
    _ = parse_input(s)
    answer = 0
    # lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
