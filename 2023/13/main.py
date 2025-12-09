import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
blocks = input_content.split('\n\n')
grids = []

def find_reflection(grid: FixedGrid, ignore_value=(None, None)):
    for x in grid.x_range:
        if x + 1 not in grid.x_range:
            break

        a, b = x, x + 1
        l, r = grid.col(a), grid.col(b)
        while l == r:
            a, b = a - 1, b + 1
            if not (a >= 0 and b < grid.width):
                if (x + 1, 1) == ignore_value:
                    break
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
                if (y + 1, 100) == ignore_value:
                    break
                return y + 1, 100
            l, r = grid.row(a), grid.row(b)

    return None, None


for block in blocks:
    grid = FixedGrid.parse(block)
    grids.append(grid)

s = 0
s2 = 0

first_reflections = []

for grid in grids:
    idx, multiplier = find_reflection(grid)
    first_reflections.append((idx, multiplier))
    s += idx * multiplier

cells = '.#'
for grid_idx, grid in enumerate(grids):
    for coord, value in grid.items():
        cell_idx = cells.index(value)
        new_value = cells[(cell_idx + 1) % len(cells)]
        grid[coord] = new_value
        idx, multiplier = find_reflection(grid, first_reflections[grid_idx])
        if idx is not None:
            s2 += idx * multiplier
            break
        grid[coord] = value

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)