import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()

# input_content = """...#......
# .......#..
# #.........
# ..........
# ......#...
# .#........
# .........#
# ..........
# .......#..
# #...#....."""

lines = input_content.split('\n')

offset = 0
for x in range(len(lines[0])):
    col = [line[x + offset] for line in lines]
    if '#' not in col:
        for y in range(len(lines)):
            lines[y] = lines[y][:x + offset] + '.' + lines[y][x + offset:]
        offset += 1

offset = 0
for y in range(len(lines)):
    row = lines[y + offset]
    if '#' not in row:
        lines.insert(y + offset, row)
        offset += 1

input_content = '\n'.join(lines)

grid = FixedGrid.parse(input_content)

s = 0
s2 = 0

galaxies = [coord for coord, value in grid.items() if value == '#']

for i in range(len(galaxies) - 1):
    for j in range(i, len(galaxies)):
        ax, ay = galaxies[i]
        bx, by = galaxies[j]

        s += abs(bx - ax) + abs(by - ay)

lib.aoc.give_answer_current(1, s)
# lib.aoc.give_answer_current(2, s2)