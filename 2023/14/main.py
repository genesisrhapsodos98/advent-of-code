import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
grid = FixedGrid.parse(input_content)

def tilt_grid(grid, direction):
    dx, dy = direction
    for coord, value in grid.items():
        if value != 'O':
            continue
        x, y = coord
        while (x + dx, y + dy) in grid:
            next_coord = (x + dx, y + dy)
            if grid[next_coord] in 'O#':
                break
            x, y = next_coord
        grid[coord] = '.'
        grid[x, y] = 'O'

def score_grid(g):
    score = 0
    rocks = [(coord, value) for coord, value in g.items() if value == 'O']
    for (x, y), _ in rocks:
        score += grid.height - y
    return score

s = 0
s2 = 0

tilt_grid(grid, (0, -1))
s += score_grid(grid)

lib.aoc.give_answer_current(1, s)
# lib.aoc.give_answer_current(2, s2)