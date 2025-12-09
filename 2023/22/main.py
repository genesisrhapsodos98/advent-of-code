import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid

def parse_input(s):
    lines = s.splitlines()
    bricks = []

    for line in lines:
        a, b = line.split('~')
        mx, my, mz = tuple(map(int, a.split(',')))
        nx, ny, nz = tuple(map(int, b.split(',')))
        brick = {(x, y, z)
                 for x in range(min(mx, nx), max(mx, nx) + 1)
                 for y in range(min(my, ny), max(my, ny) + 1)
                 for z in (mz, nz)}
        bricks.append((min(mz, nz), brick))

    bricks = [b for low_z, b in sorted(bricks)]

    settled_positions = {}
    highest_z_per_point = {}

    supporting_bricks = collections.defaultdict(set)
    supported_by = collections.defaultdict(set)

    for idx, b in enumerate(bricks):
        delta_z = min(z - highest_z_per_point.get((x, y), 0) - 1 for x, y, z in b)
        b = {(x, y, z - delta_z) for x, y, z in b}
        b_int = {(x, y, z - 1) for x, y, z in b}
        for c in b_int:
            idx2 = settled_positions.get(c)
            if idx2 is not None:
                supporting_bricks[idx2].add(idx)
                supported_by[idx].add(idx2)

        for x, y, z in b:
            settled_positions[x, y ,z] = idx
            highest_z_per_point[x, y] = max(z, highest_z_per_point.get((x, y), z))

        bricks[idx] = b

    return range(len(bricks)), supporting_bricks, supported_by

def part1(s):
    brick_ids, supporting_bricks, supported_by = parse_input(s)

    answer = 0

    for brick in brick_ids:
        if all(len(supported_by.get(supported, [])) != 1 for supported in supporting_bricks.get(brick, [])):
            answer += 1

    lib.aoc.give_answer_current(1, answer)

def part2(s):
    brick_ids, supporting_bricks, supported_by = parse_input(s)

    answer = 0

    for brick in brick_ids:
        supports_lost = { brick }
        queue = list(supporting_bricks.get(brick, []))

        while queue:
            b = queue.pop()
            if b in supports_lost:
                continue
            if all(supporting in supports_lost for supporting in supported_by.get(b, [])):
                answer += 1
                supports_lost.add(b)

                queue.extend(supporting_bricks.get(b, []))

    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
