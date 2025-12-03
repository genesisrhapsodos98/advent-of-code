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
    return lines

def get_folder_sizes(lines):
    folders = collections.defaultdict(int)
    cwd = []

    for line in lines:
        parts = line.split()
        if parts[0] == '$':
            if parts[1] == 'cd':
                if parts[2] == '..':
                    cwd.pop()
                elif parts[2] == '/':
                    cwd = ['']
                else:
                    cwd.append(parts[2])
            elif parts[1] == 'ls':
                pass
            else:
                assert(False)
        elif parts[0] == 'dir':
            pass
        else:
            size = int(parts[0])
            name = ''
            for folder in cwd:
                if name != '/':
                    name += '/'
                name += folder
                folders[name] += size

    return folders

def part1(s):
    lines = parse_input(s)
    answer = sum(size for size in get_folder_sizes(lines).values() if size <= 100000)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    lines = parse_input(s)
    folders = get_folder_sizes(lines)
    TO_FREE = 30_000_000 - (70_000_000 - folders['/'])
    answer = min(size for size in folders.values() if size >= TO_FREE)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
