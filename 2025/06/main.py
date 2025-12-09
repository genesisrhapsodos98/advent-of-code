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
    lines = s.splitlines()
    if not lines:
        return []

    max_len = max(len(line) for line in lines)
    # Pad lines
    padded_lines = [line.ljust(max_len) for line in lines]

    # Transpose to get columns
    cols = [''.join(chars) for chars in zip(*padded_lines)]

    problems = []
    current_block_cols = []

    for col in cols:
        if col.strip() == '':
            if current_block_cols:
                problems.append(current_block_cols)
                current_block_cols = []
        else:
            current_block_cols.append(col)

    if current_block_cols:
        problems.append(current_block_cols)

    parsed_problems = []
    for block_cols in problems:
        # Transpose block back to lines to find contiguous numbers horizontally
        block_lines = [''.join(chars) for chars in zip(*block_cols)]
        block_text = '\n'.join(block_lines)

        numbers = [int(n) for n in re.findall(r'\d+', block_text)]

        operator = None
        if '+' in block_text:
            operator = '+'
        elif '*' in block_text:
            operator = '*'

        if operator is None:
            # Should not happen based on problem description
            pass

        parsed_problems.append({'numbers': numbers, 'operator': operator})

    return parsed_problems


def solve_problem(problem):
    nums = problem['numbers']
    op = problem['operator']
    if op == '+':
        return sum(nums)
    elif op == '*':
        if not nums: return 0
        res = 1
        for n in nums:
            res *= n
        return res
    return 0


def part1(s):
    problems = parse_input(s)
    total = sum(solve_problem(p) for p in problems)
    lib.aoc.give_answer_current(1, total)


def parse_input_part2(s):
    lines = s.splitlines()
    if not lines:
        return []

    max_len = max(len(line) for line in lines)
    # Pad lines
    padded_lines = [line.ljust(max_len) for line in lines]

    # Transpose to get columns
    cols = [''.join(chars) for chars in zip(*padded_lines)]

    problems = []
    current_block_cols = []

    for col in cols:
        if col.strip() == '':
            if current_block_cols:
                problems.append(current_block_cols)
                current_block_cols = []
        else:
            current_block_cols.append(col)

    if current_block_cols:
        problems.append(current_block_cols)

    parsed_problems = []
    for block_cols in problems:
        # Identify operator
        operator = None
        for col in block_cols:
            for char in col:
                if char in '+*':
                    operator = char
                    break
            if operator:
                break

        numbers = []
        # Iterate columns right to left
        for col in reversed(block_cols):
            digits = [c for c in col if c.isdigit()]
            if digits:
                # Most significant digit at the top -> just join digits in order
                num_str = ''.join(digits)
                numbers.append(int(num_str))

        parsed_problems.append({'numbers': numbers, 'operator': operator})

    return parsed_problems

def part2(s):
    problems = parse_input_part2(s)
    total = sum(solve_problem(p) for p in problems)
    lib.aoc.give_answer_current(2, total)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
