import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
grid = FixedGrid.parse(input_content)

pipe_neighbors = {
    '|': [(0, -1), (0, 1)],
    '-': [(-1, 0), (1, 0)],
    'L': [(0, -1), (1, 0)],
    'J': [(0, -1), (-1, 0)],
    '7': [(-1, 0), (0, 1)],
    'F': [(1, 0), (0, 1)],
}


def find_loop(grid):
    start = next(coord for coord, pipe in grid.items() if pipe == 'S')
    positions = [start]
    loop = set()

    steps = 0

    while positions:
        loop.update(positions)
        next_positions = set()

        for x, y in positions:
            if grid[x, y] == 'S':
                cands = set(n for n in [(x - 1, y), (x, y - 1), (x, y + 1), (x + 1, y)]
                            if (n in grid and
                                grid[n] != '.' and
                                (x, y) in [(n[0] + dx, n[1] + dy) for dx, dy in pipe_neighbors[grid[n]]]))

                # Update the start tile for part 2 logic
                for t in pipe_neighbors.keys():
                    grid[x, y] = t
                    if set([(x + dx, y + dy) for dx, dy in pipe_neighbors[grid[x, y]]]) == cands:
                        break
            else:
                cands = [(x + dx, y + dy) for dx, dy in pipe_neighbors[grid[x, y]]]

            for n in cands:
                if n not in grid or n in loop:
                    continue
                next_positions.add(n)

        positions = list(next_positions)
        if len(positions) > 0:
            steps += 1

    return loop, steps


s = 0
s2 = 0

loop, steps = find_loop(grid)

s = steps
s2 = loop

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)
