import math
from collections import defaultdict

import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
grid = FixedGrid.parse(input_content)

symbol_positions = defaultdict(set)
numbers = []

s = 0
s2 = 0

for y in grid.y_range:
    num = 0
    num_border = set()

    for x in grid.x_range:
        c = grid[x, y]
        if c.isdigit():
            if num == 0:
                num_border |= {(x - 1, y - 1), (x - 1, y), (x - 1, y + 1)}

            num = 10 * num + int(c)
            num_border |= {(x, y - 1), (x, y + 1)}
        else:
            if num > 0:
                # Add the border on the right
                num_border |= {(x, y - 1), (x, y), (x, y + 1)}
                numbers.append((num, num_border))
                num = 0
                num_border = set()
            if c != '.':
                symbol_positions[c].add((x, y))

    if num > 0:
        num_border |= {(grid.width, y - 1), (grid.width, y), (grid.width, y + 1)}
        numbers.append((num, num_border))

symbols = set()
for places in symbol_positions.values():
    symbols |=  places

s = sum(n for n, border in numbers if len(border & symbols) > 0)

gears = defaultdict(list)

for n, border in numbers:
    for coords in border & symbol_positions['*']:
        gears[coords].append(n)

s2 = sum(math.prod(gear_nums) for gear_nums in gears.values() if len(gear_nums) == 2)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)