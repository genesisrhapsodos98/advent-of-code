import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
# input_content = """R 6 (#70c710)
# D 5 (#0dc571)
# L 2 (#5713f0)
# D 2 (#d2c081)
# R 2 (#59c680)
# D 2 (#411b91)
# L 5 (#8ceee2)
# U 2 (#caa173)
# L 1 (#1b58a2)
# U 2 (#caa171)
# R 2 (#7807d2)
# U 3 (#a77fa3)
# L 2 (#015232)
# U 2 (#7a21e3)"""
lines = input_content.split('\n')

dig_plans = []
directions = {
    'U': (0, -1),
    'D': (0, 1),
    'L': (-1, 0),
    'R': (1, 0),
}

for line in lines:
    a, b, c = line.split()
    dig_plans.append((a, int(b), c))

s = 0
s2 = 0

current_pos = (0, 0)
visited_pos = [(0, 0)]

for plan in dig_plans:
    d, length, hex_code = plan
    dx, dy = directions[d]
    for _ in range(length):
        x, y = current_pos
        current_pos = x + dx, y + dy
        visited_pos.append(current_pos)

min_x = min([x for x, y in visited_pos])
min_y = min([y for x, y in visited_pos])

transposed_pos = [(x - min_x, y - min_y) for x, y in visited_pos]
grid_dict = dict((pos, '#') for pos in transposed_pos)

grid = FixedGrid.from_dict(grid_dict, missing='.')

seen = set(transposed_pos)
fill = set(seen)

s = 0
s2 = 0

for y in grid.y_range:
    is_enclosed = False
    for x in grid.x_range:
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

for coord in fill:

s += sum([1 for _, cell in grid.items() if cell == '#'])

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)