import collections

import lib.aoc
import lib.grid

def parse_input(s):
    return lib.grid.FixedGrid.parse(s)

def preprocess_splitters(grid):
    cols = {x: [] for x in grid.x_range}
    for (x, y), val in grid.items():
        if val == '^':
            cols[x].append(y)
    for x in cols:
        cols[x].sort()
    return cols


def next_splitter_below(splitters, x, y):
    ys = splitters.get(x)
    if not ys:
        return None

    lo, hi = 0, len(ys)
    while lo < hi:
        mid = (lo + hi) // 2
        if ys[mid] > y:
            hi = mid
        else:
            lo = mid + 1

    if lo < len(ys):
        return ys[lo]
    return None


def simulate_splits_fast(grid):
    sx, sy = grid.find('S')

    splitters = preprocess_splitters(grid)

    first_y = next_splitter_below(splitters, sx, sy)
    if first_y is None:
        return 0

    seen = set()
    stack = [(sx, first_y)]

    while stack:
        x, y = stack.pop()

        if (x, y) in seen:
            continue
        seen.add((x, y))

        nx = x - 1
        ny = next_splitter_below(splitters, nx, y)
        if ny is not None:
            stack.append((nx, ny))

        nx = x + 1
        ny = next_splitter_below(splitters, nx, y)
        if ny is not None:
            stack.append((nx, ny))

    return len(seen)


def part1(s):
    grid = parse_input(s)
    answer = simulate_splits_fast(grid)
    lib.aoc.give_answer_current(1, answer)

def quantum_timelines(grid) -> int:
    start = grid.find('S')

    sx, sy = start

    timelines = collections.defaultdict(int)
    timelines[sx] = 1

    for y in range(sy + 1, grid.height):
        next_row = collections.defaultdict(int)
        for x, count in timelines.items():
            if (x, y) not in grid:
                continue
            cell = grid[x, y]
            if cell == '^':
                if x - 1 >= 0:
                    next_row[x - 1] += count
                if x + 1 < grid.width:
                    next_row[x + 1] += count
            elif cell == '.':
                next_row[x] += count
        timelines = next_row

    return sum(timelines.values())

def part2(s):
    grid = parse_input(s)
    answer = quantum_timelines(grid)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
