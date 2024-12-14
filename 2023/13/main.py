import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
blocks = input_content.split('\n\n')
grids = []

def find_reflection(grid: FixedGrid):
    for x in grid.x_range:
        if x + 1 not in grid.x_range:
            break

        a, b = x, x + 1
        l, r = grid.col(a), grid.col(b)
        while l == r:
            a, b = a - 1, b + 1
            if not (a >= 0 and b < grid.width):
                return x + 1, 1
            l, r = grid.col(a), grid.col(b)

    for y in grid.y_range:
        if y + 1 not in grid.y_range:
            break

        a, b = y, y + 1
        l, r = grid.row(a),  grid.row(b)
        while l == r:
            a, b = a - 1, b + 1
            if not (a >= 0 and b < grid.height):
                return y + 1, 100
            l, r = grid.row(a), grid.row(b)

    return None, None


for block in blocks:
    grid = FixedGrid.parse(block)
    grids.append(grid)

s = 0
s2 = 0

for grid in grids:
    idx, multiplier = find_reflection(grid)
    s += idx * multiplier

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)