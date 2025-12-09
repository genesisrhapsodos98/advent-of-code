import collections
import functools
import itertools
import math
import re

import sympy

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
    hailstones = parse_input(s)

    x = sympy.var('x')
    y = sympy.var('y')
    z = sympy.var('z')

    vx = sympy.var('vx')
    vy = sympy.var('vy')
    vz = sympy.var('vz')

    equations = []

    for idx, (p, v) in enumerate(hailstones[:3]):
        t = sympy.var(f't{idx}')

        equations.append(sympy.Eq(x + t * vx, p.x + v.x * t))
        equations.append(sympy.Eq(y + t * vy, p.y + v.y * t))
        equations.append(sympy.Eq(z + t * vz, p.z + v.z * t))

    d = sympy.solve(equations)[0]
    answer = sum(d[v] for v in (x, y, z))
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
