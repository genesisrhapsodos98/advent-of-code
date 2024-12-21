import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid
from lib.graphics import *

visited = dict()

def cheapest_arrow_pad(curr, curc, destr, destc, n_robots):
    answer = math.inf

    state = (curr, curc, destr, destc, n_robots)

    if state in visited:
        return visited[(curr, curc, destr, destc, n_robots)]

    queue = [(curr, curc, '')]
    while queue:
        r, c, presses = queue.pop(0)
        if r == destr and c == destc:
            rec = cheapest_robot(presses + 'A', n_robots - 1)
            answer = min(answer, rec)
            continue

        if r == 0 and c == 0:
            continue

        else:
            if r < destr:
                queue.append((r + 1, c, presses + 'v'))
            elif r > destr:
                queue.append((r -1, c, presses + '^'))
            if c < destc:
                queue.append((r, c + 1, presses + '>'))
            elif c > destc:
                queue.append((r, c - 1, presses + '<'))

    visited[state] = answer
    return answer

def cheapest_robot(presses, n_robots):
    if n_robots == 1:
        return len(presses)

    result = 0
    pad_config = 'X^A<v>'

    curr = 0
    curc = 2

    for i in range(len(presses)):
        for nextr in range(0, 2):
            for nextc in range(0, 3):
                if pad_config[nextr * 3 + nextc] == presses[i]:
                    result += cheapest_arrow_pad(curr, curc, nextr, nextc, n_robots)
                    curr = nextr
                    curc = nextc

    return result

def cheapest(curr, curc, destr, destc, n_robots):
    answer = math.inf
    queue = [(curr, curc, '')]

    while queue:
        r, c, presses = queue.pop(0)
        if r == destr and c == destc:
            rec = cheapest_robot(presses + 'A', n_robots)
            answer = min(answer, rec)
            continue

        if r == 3 and c == 0:
            continue

        else:
            if r < destr:
                queue.append((r + 1, c, presses + 'v'))
            elif r > destr:
                queue.append((r - 1, c, presses + '^'))
            if c < destc:
                queue.append((r, c + 1, presses + '>'))
            elif c > destc:
                queue.append((r, c - 1, presses + '<'))


    return answer

def solve(codes, n_robots):
    sum = 0
    pad_config = '789456123X0A'

    curr = 3
    curc = 2

    for code in codes:
        result = 0
        for i in range(len(code)):
            for nextr in range(0, 4):
                for nextc in range(0, 3):
                    if pad_config[nextr * 3 + nextc] == code[i]:
                        result += cheapest(curr, curc, nextr, nextc, n_robots)
                        curr = nextr
                        curc = nextc

        sum += result * int(code[:-1])

    return sum



def parse_input(s):
    codes = s.splitlines()
    return codes

def part1(s):
    codes = parse_input(s)
    answer = solve(codes, 3)
    lib.aoc.give_answer_current(1, answer)


def part2(s):
    codes = parse_input(s)
    answer = solve(codes, 26)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
