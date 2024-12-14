import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()

grid = FixedGrid.parse(input_content)
lines = input_content.split('\n')

empty_cols = set()
empty_rows = set()

for x in grid.x_range:
    col = grid.col(x)
    if '#' not in col:
        empty_cols.add(x)

for y in grid.y_range:
    row = grid.row(y)
    if '#' not in row:
        empty_rows.add(y)

s = 0
s2 = 0

galaxies = [coord for coord, value in grid.items() if value == '#']

for i in range(len(galaxies) - 1):
    for j in range(i + 1, len(galaxies)):
        ax, ay = galaxies[i]
        bx, by = galaxies[j]

        added_cols = sum([1 for c in range(min(ax, bx), max(ax, bx)) if c in empty_cols])
        added_rows = sum([1 for r in range(min(ay, by), max(ay, by)) if r in empty_rows])

        s += abs(bx - ax) + abs(by - ay) + added_rows + added_cols
        s2 += abs(bx - ax) + abs(by - ay) + 999999 * added_rows + 999999 * added_cols

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)