import collections

import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()

grid = FixedGrid.parse(input_content)

s = sum(1 for coords, direction in grid.find_matches('XMAS', include_diagonals=True, allow_reverse=True))

cross_count = collections.Counter()
for (x, y), (dx, dy) in grid.find_matches('MAS', include_orthogonals=False, include_diagonals=True, allow_reverse=True):
    cross_count[x + dx, y + dy] += 1

s2 = sum(1 for value in cross_count.values() if value == 2)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)
