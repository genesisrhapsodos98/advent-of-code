import collections
import functools
import itertools
import json
import math
import parse
import re2 as re
import sympy # sympy.parse_expr, sympy.solve, sympy.Eq
import sys # sys.setrecursionlimit(1000000)
import z3 # x = z3.Int('x'); x < 0; (x-1) >= 0
# z3.If(x >= 0, x, -x); z3.And(); z3.Or(); z3.Not()
# s = z3.Solver(); solver.add(constraint); s.check(); s.model()[x].as_long()
# o = z3.Optimize(); o.minimize(x); o.check(); o.model()[x].as_long()

import lib.algorithms
import lib.aoc
import lib.cyk
import lib.graph
from lib.graphics import *
import lib.grid
import lib.hex_coord
import lib.lazy_dict
import lib.math
import lib.ocr
import lib.parsing

def parse_input(s):
    banks = s.splitlines()
    return banks

def max_k_digits(s: str, k: int) -> str:
    n = len(s)
    if k > n:
        raise ValueError("Not enough digits to pick k digits")

    result = []
    start = 0

    for remaining in range(k, 0, -1):
        # Last possible index for current digit
        end = n - remaining
        # Pick the maximum digit in s[start:end+1]
        best_digit = max(s[start:end+1])
        best_index = s.find(best_digit, start, end+1)
        result.append(best_digit)
        start = best_index + 1

    return int("".join(result))

def part1(s):
    banks = parse_input(s)

    answer = 0
    for bank in banks:
        answer += max_k_digits(bank, 2)

    lib.aoc.give_answer_current(1, answer)

def part2(s):
    banks = parse_input(s)

    answer = 0
    for bank in banks:
        x = max_k_digits(bank, 12)
        answer += x
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
