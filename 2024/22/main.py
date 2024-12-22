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

@functools.cache
def mix(num, val):
    return val ^ num

@functools.cache
def prune(num):
    return num % 16777216

@functools.cache
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
    numbers = parse_input(s)
    prices = []
    differences = []
    answer = 0
    occurrences = []
    all_occurrences = set()

    for idx, num in enumerate(numbers):
        final = num
        prices.append([num % 10])
        differences.append([None])
        occurrences.append(dict())
        for i in range(2000):
            final = randomize(final)
            new_price = final % 10
            prices[idx].append(new_price)
            differences[idx].append(new_price - prices[idx][-2])
            if len(differences[idx]) > 4:
                key = (differences[idx][-4], differences[idx][-3], differences[idx][-2], differences[idx][-1])
                all_occurrences.add(key)
                if key not in occurrences[idx]:
                    occurrences[idx][key] = new_price

    best_value = 0
    for occ in all_occurrences:
        occ_value = 0
        for idx, num in enumerate(numbers):
            if occ not in occurrences[idx]:
                continue
            first_occurrence_price = occurrences[idx][occ]
            occ_value += first_occurrence_price
        if occ_value > best_value:
            best_value = occ_value

    answer = best_value

    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
