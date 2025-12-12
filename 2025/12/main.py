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

def parse_input(s: str):
    lines = [line.rstrip("\n") for line in s.splitlines()]
    i = 0
    shapes = {}

    # Parse shapes
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1
            continue

        m = re.match(r"^(\d+):\s*$", line)
        if not m:
            # First non-shape line: start of regions section
            break

        idx = int(m.group(1))
        i += 1
        grid_lines = []
        while i < len(lines):
            cur = lines[i]
            if not cur.strip():
                i += 1
                break
            # If we see another shape header, stop this shape;
            # the outer loop will pick it up again.
            if re.match(r"^\d+:\s*$", cur.strip()):
                break
            grid_lines.append(cur)
            i += 1
        shapes[idx] = grid_lines

    # Parse regions from current i onward
    regions = []
    while i < len(lines):
        line = lines[i].strip()
        i += 1
        if not line:
            continue
        left, right = line.split(":")
        dims = left.strip()
        w_str, h_str = dims.split("x")
        w = int(w_str)
        h = int(h_str)
        counts = [int(x) for x in right.strip().split()]
        regions.append((w, h, counts))

    return shapes, regions

# Read the grid of a shape and return its coordinates
def shape_coords(grid_lines):
    coords = []
    for y, row in enumerate(grid_lines):
        for x, c in enumerate(row):
            if c == "#":
                coords.append((x, y))
    if not coords:
        return []
    return normalize(coords)


# Rotate the shape 90 degrees clockwise
def rotate_90(coords):
    return [(-y, x) for x, y in coords]

# Mirror the shape horizontally
def flip_x(coords):
    return [(-x, y) for x, y in coords]


# Normalize the coordinate of the shape so that top left corner is (0, 0)
def normalize(coords):
    min_x = min(x for x, _ in coords)
    min_y = min(y for _, y in coords)
    return [(x - min_x, y - min_y) for x, y in coords]

# Generate all orientations of a shape by trying all 4 rotations * 2 mirrored states
def all_orientations(base_coords):
    seen = set()
    result = []
    cur = base_coords
    for _ in range(4):
        for variant in (cur, flip_x(cur)):
            norm = normalize(variant)
            key = tuple(sorted(norm))
            if key not in seen:
                seen.add(key)
                result.append(norm)
        cur = rotate_90(cur)
    return result


def build_placements(shapes, w, h):
    shapes_orients = {}
    shapes_areas = {}
    for idx, grid in shapes.items():
        base = shape_coords(grid)
        orients = all_orientations(base)
        shapes_orients[idx] = orients
        shapes_areas[idx] = len(base)

    placements = {idx: [] for idx in shapes.keys()}

    for idx, orients in shapes_orients.items():
        for coords in orients:
            max_x = max(x for x, _ in coords)
            max_y = max(y for _, y in coords)
            if max_x + 1 > w or max_y + 1 > h:
                continue
            # Try all possible placements with offset (ox, oy) from top left corner
            for oy in range(h - max_y):
                for ox in range(w - max_x):
                    mask = 0
                    for dx, dy in coords:
                        x = ox + dx
                        y = oy + dy
                        # Store occupied cells in a bit mask
                        bit = y * w + x
                        mask |= 1 << bit
                    placements[idx].append(mask)

    return placements, shapes_areas


def can_fill_region(w, h, counts, placements, shapes_areas):
    pieces = []
    for idx, cnt in enumerate(counts):
        for _ in range(cnt):
            pieces.append(idx)
    if not pieces:
        return True

    pieces.sort(key=lambda idx: -shapes_areas[idx])

    # Precompute total area of shapes and area of region. If the region is too small, fail early.
    total_cells = w * h
    total_area = sum(shapes_areas[idx] for idx in pieces)
    if total_area > total_cells:
        return False

    remaining_area_suffix = [0] * (len(pieces) + 1)
    for i in range(len(pieces) - 1, -1, -1):
        remaining_area_suffix[i] = remaining_area_suffix[i + 1] + shapes_areas[pieces[i]]

    def backtrack(i, occupied):
        # All pieces have been placed
        if i == len(pieces):
            return True

        # Check for free space to fail early, pruning this branch when possible
        free_cells = total_cells - occupied.bit_count()
        if free_cells < remaining_area_suffix[i]:
            return False

        # Check for collisions with existing pieces, if not then use bitwise OR to place piece to the bitmask
        idx = pieces[i]
        for pmask in placements[idx]:
            if pmask & occupied:
                continue
            if backtrack(i + 1, occupied | pmask):
                return True
        return False

    return backtrack(0, 0)


def part1(s: str):
    shapes, regions = parse_input(s)
    answer = 0
    for w, h, counts in regions:
        placements, shapes_areas = build_placements(shapes, w, h)
        if can_fill_region(w, h, counts, placements, shapes_areas):
            answer += 1
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    print('Is there a part 2? Unsure until we see it!')
    lib.aoc.give_answer_current(2, 1)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
