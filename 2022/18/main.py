import collections

import lib.algorithms
import lib.aoc
import lib.cyk
import lib.graph
import lib.grid
import lib.hex_coord
import lib.lazy_dict
import lib.math
import lib.ocr
import lib.parsing
from lib.graphics import *


# z3.If(x >= 0, x, -x); z3.And(); z3.Or(); z3.Not()
# s = z3.Solver(); solver.add(constraint); s.check(); s.model()[x].as_long()
# o = z3.Optimize(); o.minimize(x); o.check(); o.model()[x].as_long()

def parse_input(s):
    cubes = set()
    for line in s.splitlines():
        x, y, z = map(int, line.strip().split(','))
        cubes.add(Vec3D(x, y, z))
    return cubes

dirs = [X_AXIS, -X_AXIS, Y_AXIS, -Y_AXIS, Z_AXIS, -Z_AXIS]

def part1(s):
    cubes = parse_input(s)
    answer = 0
    for cube in cubes:
        for d in dirs:
            if cube + d not in cubes:
                answer += 1
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    cubes = parse_input(s)

    min_x = min(c.x for c in cubes) - 1
    max_x = max(c.x for c in cubes) + 1
    min_y = min(c.y for c in cubes) - 1
    max_y = max(c.y for c in cubes) + 1
    min_z = min(c.z for c in cubes) - 1
    max_z = max(c.z for c in cubes) + 1

    start = Vec3D(min_x, min_y, min_z)
    visited = {start}
    queue = collections.deque([start])

    answer = 0

    while queue:
        cube = queue.popleft()
        for d in dirs:
            neighbor = cube + d
            if neighbor in cubes:
                answer += 1
            elif (min_x <= neighbor.x <= max_x and
                  min_y <= neighbor.y <= max_y and
                  min_z <= neighbor.z <= max_z and
                  neighbor not in visited):
                visited.add(neighbor)
                queue.append(neighbor)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
