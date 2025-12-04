import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
grid = FixedGrid.parse(input_content)
grid2 = FixedGrid.parse(input_content)

def ns_roll(grid, dy):
    y_range = grid.y_range[::-dy]
    for x in grid.x_range:
        dest = y_range[0]
        for y, c in zip(y_range, grid.col(x)[::-dy]):
            if c == 'O':
                if y != dest:
                    grid[x,y] = '.'
                    grid[x,dest] = 'O'
                dest -= dy
            elif c == '#':
                dest = y-dy

def ew_roll(grid, dx):
    x_range = grid.x_range[::-dx]
    for y in grid.y_range:
        dest = x_range[0]
        for x, c in zip(x_range, grid.row(y)[::-dx]):
            if c == 'O':
                if x != dest:
                    grid[x,y] = '.'
                    grid[dest,y] = 'O'
                dest -= dx
            elif c == '#':
                dest = x-dx

def score_grid(g):
    score = 0
    rocks = [(coord, value) for coord, value in g.items() if value == 'O']
    for (x, y), _ in rocks:
        score += grid.height - y
    return score

def run_cycle(grid):
    ns_roll(grid, -1)  # North
    ew_roll(grid, -1)  # West
    ns_roll(grid, 1)  # South
    ew_roll(grid, 1)  # East

s = 0
s2 = 0

ns_roll(grid, -1)
s += score_grid(grid)

CYCLES = 1000000000

seen = {input_content: 0}
record = [input_content]

cycle = 0

while cycle < CYCLES:
    cycle += 1
    run_cycle(grid2)
    key = grid2.as_str('')

    if key in seen:
        last = seen[key]
        delta = cycle - last

        # Jump straight to the final answer
        cycle_off = (CYCLES - cycle) % delta
        final_state_idx = last + cycle_off

        # Reparse the final state since only the key was saved
        grid2 = lib.grid.FixedGrid.parse(record[final_state_idx])

        break

    seen[key] = cycle
    record.append(key)

s2 += score_grid(grid2)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)