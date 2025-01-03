from typing import Generator, Any

import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

def parse_input(input_str: str):
    for line in input_str.splitlines():
        a, b, c = line.split()
        yield a, int(b)

def parse_input_2(input_str: str):
    for line in input_str.splitlines():
        _, _, c = line.split()
        num = int(c[2:-1], base=16)
        yield 'RDLU'[num&0xF], num // 16

def solve(sequence: Generator[tuple[str, int], Any, None]):
    x, y = 0, 0

    corners = [(x, y)]

    x_points = set()
    y_points = set()

    for d, num in sequence:
        if d == 'U':
            y -= num
        elif d == 'D':
            y += num
        elif d == 'R':
            x += num
        else:
            x -= num

        corners.append((x, y))
        x_points.add(x)
        y_points.add(y)

    x_points = sorted(x_points)
    y_points = sorted(y_points)

    compression = {}

    grid_sizes = {}

    new_x = 0

    for ix, x in enumerate(x_points):
        new_y = 0
        for iy, y in enumerate(y_points):
            compression[x, y] = (new_x, new_y)

            grid_sizes[new_x, new_y] = 1

            if ix > 0:
                last_x = x_points[ix - 1]
                grid_sizes[new_x - 1, new_y] = (x - last_x - 1)
                if iy > 0:
                    last_y = y_points[iy - 1]
                    grid_sizes[new_x - 1, new_y - 1] = (x - last_x - 1) * (y - last_y - 1)
            if iy > 0:
                last_y = y_points[iy - 1]
                grid_sizes[new_x, new_y - 1] = (y - last_y - 1)

            new_y += 2

        new_x += 2

    seen = set()

    for (e0, e1) in zip(corners, corners[1:] + [corners[0]]):
        x0, y0 = compression[e0]
        x1, y1 = compression[e1]

        if x0 > x1:
            x0, x1 = x1, x0
        if y0 > y1:
            y0, y1 = y1, y0

        for x in range(x0, x1 + 1):
            for y in range(y0, y1 + 1):
                seen.add((x, y))

    min_x = min(x for x, y in seen)
    max_x = max(x for x, y in seen)
    min_y = min(y for x, y in seen)
    max_y = max(y for x, y in seen)

    x_range = range(min_x, max_x + 1)
    y_range = range(min_y, max_y + 1)

    fill = set(seen)

    for y in y_range:
        is_enclosed = False
        for x in x_range:
            if (x, y) in seen:
                if (x, y - 1) in seen and (x, y + 1) in seen:
                    is_enclosed = not is_enclosed
                elif (x, y + 1) in seen and (x + 1, y) in seen:
                    is_enclosed = not is_enclosed
                elif (x, y + 1) in seen and (x - 1, y) in seen:
                    is_enclosed = not is_enclosed
            else:
                if is_enclosed:
                    fill.add((x, y))

    return sum(map(grid_sizes.__getitem__, fill))

s = solve(parse_input(input_content))
s2 = solve(parse_input_2(input_content))


lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)