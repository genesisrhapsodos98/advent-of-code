import collections
import functools
import itertools
import json
import math
import operator

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

class Monkey:
    def __init__(self, spec):
        lines = list(map(str.strip, spec.splitlines()))
        self.number = int(lines[0].split()[1][:-1])
        self.items = list(map(int, lines[1].split(': ')[1].split(', ')))

        # Parse the operation into lambda functions
        # It's tedious, but runs much faster (and feels better than using eval!)
        left, op, right = lines[2].split('new = ')[1].split()
        assert(left == 'old')
        binary_ops = {'*': operator.mul, '+': operator.add}
        op = binary_ops[op]
        if right == 'old':
            self.op = lambda worry: op(worry, worry)
        else:
            self.op = lambda worry: op(worry, int(right))

        self.divisor = int(lines[3].split()[-1])
        self.true_dest = int(lines[4].split()[-1])
        self.false_dest = int(lines[5].split()[-1])
        self.inspections = 0

    def inspect_items(self, mod_by, div_by):
        inspected = map(self.op, self.items)
        if div_by is not None:
            inspected = [worry // div_by for worry in inspected]
        else:
            # Only apply mod_by if we are *not* repeatedly dividing
            # Division and mod_by can conflict with each other due to repeated division!
            inspected = [worry % mod_by for worry in inspected]

        self.items = []
        self.inspections += len(inspected)

        for worry in inspected:
            if worry % self.divisor == 0:
                yield worry, self.true_dest
            else:
                yield worry, self.false_dest

def parse_input(s):
    monkeys = list(map(Monkey, s.split('\n\n')))
    return monkeys

def solve(monkeys, rounds, div_by=None):
    mod_by = math.lcm(*[m.divisor for m in monkeys])

    for _ in range(rounds):
        for m in monkeys:
            for worry, dest in m.inspect_items(mod_by, div_by):
                monkeys[dest].items.append(worry)

    a, b = sorted(m.inspections for m in monkeys)[-2:]
    return a * b

def part1(s):
    monkeys = parse_input(s)
    answer = solve(monkeys, 20, 3)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    monkeys = parse_input(s)
    answer = solve(monkeys, 10_000)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
