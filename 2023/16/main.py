from collections import defaultdict

import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
grid = FixedGrid.parse(input_content)

def move_next(grid, head):
    (x, y), (dx, dy) = head

    next_pos = x + dx, y + dy
    nx, ny = next_pos
    if next_pos not in grid or (dx, dy) == (0, 0):
        return []

    element = grid[next_pos]
    result = []
    match element:
        case '.':
            result = [((nx, ny), (dx, dy))]
        case '/':
            dx, dy = -dy, -dx
            result = [((nx, ny), (dx, dy))]
        case '\\':
            dx, dy = dy, dx
            result = [((nx, ny), (dx, dy))]
        case '|':
            if dx == 0:
                result = [((nx, ny), (dx, dy))]
            else:
                up_head = (nx, ny), (0, -1)
                down_head = (nx, ny), (0, 1)
                result =[up_head, down_head]
        case '-':
            if dy == 0:
                result = [((nx, ny), (dx, dy))]
            else:
                left_head = (nx , ny), (-1, 0)
                right_head = (nx , ny), (1, 0)
                result = [left_head, right_head]
    result = [r for r in result if r[0] in grid]
    return result

def energize(grid, start= ((-1, 0), (1, 0))):
    cur, cur_direction = start
    beams = defaultdict(set)
    energized = set()

    heads = [(cur, cur_direction)]

    while len(heads) > 0:
        head = heads.pop(0)

        if head in beams:
            continue

        if head[0] in grid:
            energized.add(head[0])
            beams[head].add(True)

        new_heads = move_next(grid, head)
        heads.extend(new_heads)

    return len(energized)


s = 0
s2 = 0

s = energize(grid)

alt_starts = []

for x in grid.x_range:
    alt_starts.append(((x, -1), (0, 1)))
    alt_starts.append(((x, grid.height), (0, -1)))
for y in grid.y_range:
    alt_starts.append(((-1, y), (1, 0)))
    alt_starts.append(((grid.width, y), (-1, 0)))

best = s
for st in alt_starts:
    energized = energize(grid, st)
    if energized > best:
        best = energized

s2 = best

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)