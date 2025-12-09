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
    return list(map(int, s.splitlines()))


def solve(s, decryption_key=1, rounds=1):
    nums = parse_input(s)
    nums = [x * decryption_key for x in nums]

    # Use tuples (val, original_index) to handle duplicates and track original order
    mixed = [(x, i) for i, x in enumerate(nums)]
    original_order = list(mixed)
    N = len(mixed)

    for _ in range(rounds):
        for item in original_order:
            current_idx = mixed.index(item)

            # Remove the item, effectively reducing list size to N-1
            mixed.pop(current_idx)

            val = item[0]
            # Calculate new index in the list of size N-1
            # The % operator in Python handles negative numbers correctly (wrapping around)
            new_idx = (current_idx + val) % (N - 1)

            # Insert the item back at the new position
            mixed.insert(new_idx, item)

    # Find the tuple with value 0
    zero_tuple = next(x for x in mixed if x[0] == 0)
    zero_idx = mixed.index(zero_tuple)

    c1 = mixed[(zero_idx + 1000) % N][0]
    c2 = mixed[(zero_idx + 2000) % N][0]
    c3 = mixed[(zero_idx + 3000) % N][0]

    return c1 + c2 + c3

def part1(s):
    answer = solve(s, decryption_key=1, rounds=1)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    answer = solve(s, decryption_key=811589153, rounds=10)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
