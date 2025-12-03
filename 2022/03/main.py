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
    rucksacks = s.splitlines()
    return rucksacks

priorities = '.abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'

def part1(s):
    rucksacks = parse_input(s)
    answer = 0
    for rucksack in rucksacks:
        half, rem = divmod(len(rucksack), 2)
        left, right = rucksack[:half + rem], rucksack[half+rem:]
        for item in set(left):
            if item in right:
                answer += priorities.index(item)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    rucksacks = parse_input(s)
    groups = [rucksacks[i:i+3] for i in range(0, len(rucksacks), 3)]
    answer = 0
    for group in groups:
        items = [set(rucksack) for rucksack in group]
        badge = list(functools.reduce(set.intersection, items))[0]
        answer += priorities.index(badge)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
# INPUT = '''vJrwpWtwJgWrhcsFMMfFFhFp
# jqHRNqRjqzjGDLGLrsFMfFZSrLrFZsSL
# PmmdzqPrVvPwwTWBwg
# wMqvLMZHhHMvwLHjbvcjnnSBnvTQFn
# ttgJtRGJQctTZtZT
# CrZsJsPPZsGzwwsLwLmpwMDw'''
part1(INPUT)
part2(INPUT)
