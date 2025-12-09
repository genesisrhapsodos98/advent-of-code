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

# Count enclosed tiles by tracking parity per row
# If an odd number of vertical tiles have been seen then any ground tiles
# are enclosed, otherwise they are outside. This is similar to checking
# if an arbitrary point is enclosed n an arbitrary polygon.
for y in grid.y_range:
    is_enclosed = False
    for x in grid.x_range:
        if (x, y) in loop:
            # Note: | is obviously a vertical pipe
            # A "complex" vertical pipe must have one of (but not both of)
            # F and 7. FJ and L7 are "complex" vertical pipes, but F7 and
            # LJ are both turnarounds and should *not* count!
            if grid[x,y] in '|F7':
                is_enclosed = not is_enclosed
        else:
            if is_enclosed:
                s2 += 1

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)
