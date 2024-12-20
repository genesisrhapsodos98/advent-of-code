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
    hailstones = []
    for line in lines:
        a, b = line.split(' @ ')
        position = tuple(map(int, a.split(', ')))
        velocity = tuple(map(int, b.split(', ')))
        p = Point3D(*position)
        v = Vec3D(*velocity)
        hailstones.append((p, v))
    return hailstones

def part1(s):
    hailstones = parse_input(s)

    MIN = 200000000000000
    MAX = 400000000000000

    answer = 0

    for idx, (p1, v1) in enumerate(hailstones):
        for p2, v2 in hailstones[idx + 1:]:
            a = v1.y / v1.x
            denom = a * v2.x - v2.y
            if denom == 0:
                continue

            t2 = (p2.y - p1.y + a * p1.x - a * p2.x) / denom
            if t2 < 0:
                continue

            t1 = (p2.x + v2.x * t2 - p1.x) / v1.x
            if t1 < 0:
                continue

            collision = p1 + v1 * t1
            if MIN <= collision.x <= MAX and MIN <= collision.y <= MAX:
                answer += 1

    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
    _ = parse_input(s)
    answer = 0
    # lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
