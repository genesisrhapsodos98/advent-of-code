import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()

grid_content, movements_content = input_content.split('\n\n')
new_grid_content = (grid_content
                    .replace('#', '##')
                    .replace('O', '[]')
                    .replace('.', '..')
                    .replace('@', '@.'))
new_grid = FixedGrid.parse(new_grid_content)
movements = ''.join(movements_content.split('\n'))
grid = FixedGrid.parse(grid_content)

s = 0
s2 = 0

x, y = grid.find("@")
grid[x, y] = '.'
moves = {
    '<': (-1, 0),
    '^': (0, -1),
    '>': (1, 0),
    'v': (0, 1)
}

for move in movements:
    dx, dy = moves[move]
    nx, ny = x + dx, y + dy

    if (nx, ny) not in grid or grid[nx, ny] == '#':
        continue

    if grid[nx, ny] == '.':
        x, y = nx, ny
        continue

    if grid[nx, ny] == 'O':
        px, py = nx, ny
        while grid[px, py] == 'O':
            px, py = px + dx, py + dy

        if grid[px, py] == '#':
            continue

        while (px, py) != (nx, ny):
            grid[px, py] = 'O'
            px, py = px - dx, py - dy

        grid[nx, ny] = '.'
        x, y = nx, ny

def eval_grid(grid, box_elem='O'):
    boxes_pos = [coord for coord, value in grid.items() if value == box_elem]
    answer = 0
    for x, y in boxes_pos:
        answer += 100 * y + x
    return answer

s = eval_grid(grid)

x, y = new_grid.find('@')
new_grid[x, y] = '.'

for move in movements:
    dx, dy = moves[move]
    nx, ny = x + dx, y + dy

    if (nx, ny) not in new_grid or new_grid[nx, ny] == '#':
        continue

    if new_grid[nx, ny] == '.':
        x, y = nx, ny
        continue

    if new_grid[nx, ny] in '[]':
        boxes_pos = set()
        other_part = (nx - 1, ny) if new_grid[nx, ny] == ']' else (nx + 1, ny)
        boxes_pos.add((nx, ny))
        boxes_pos.add(other_part)

        leftmost = min([x for x, y in boxes_pos])
        rightmost = max([x for x, y in boxes_pos])
        topmost = min([y for x, y in boxes_pos])
        bottommost = max([y for x, y in boxes_pos])

        if (dx, dy) == (1, 0):
            edge_boxes = set([pos for pos in boxes_pos if pos[0] == rightmost])
        elif (dx, dy) == (-1, 0):
            edge_boxes = set([pos for pos in boxes_pos if pos[0] == leftmost])
        elif (dx, dy) == (0, 1):
            edge_boxes = set([pos for pos in boxes_pos if pos[1] == bottommost])
        else:
            edge_boxes = set([pos for pos in boxes_pos if pos[1] == topmost])

        can_move = True
        while len(edge_boxes) > 0:
            new_edge_boxes = set()
            for box in edge_boxes:
                bx, by = box
                px, py = bx + dx, by + dy

                if new_grid[px, py] == '#':
                    new_edge_boxes = set()
                    can_move = False
                    break

                if new_grid[px, py] in '[]':
                    other_part = (px - 1, py) if new_grid[px, py] == ']' else (px + 1, py)
                    new_edge_boxes.add((px, py))
                    new_edge_boxes.add(other_part)
                    boxes_pos.add((px, py))
                    boxes_pos.add(other_part)

            edge_boxes = new_edge_boxes
            if len(edge_boxes) == 0:
                break

            leftmost = min([x for x, y in edge_boxes])
            rightmost = max([x for x, y in edge_boxes])
            topmost = min([y for x, y in edge_boxes])
            bottommost = max([y for x, y in edge_boxes])
            if (dx, dy) == (1, 0):
                edge_boxes = set([pos for pos in edge_boxes if pos[0] == rightmost])
            elif (dx, dy) == (-1, 0):
                edge_boxes = set([pos for pos in edge_boxes if pos[0] == leftmost])
            elif (dx, dy) == (0, 1):
                edge_boxes = set([pos for pos in edge_boxes if pos[1] == bottommost])
            else:
                edge_boxes = set([pos for pos in edge_boxes if pos[1] == topmost])

        if not can_move:
            continue

        replacements = []
        for bx, by in boxes_pos:
            elem = new_grid[bx, by]
            replacements.append(((bx + dx, by + dy), elem))
        for pos in boxes_pos:
            new_grid[pos] = '.'
        for pos, elem in replacements:
            new_grid[pos] = elem
        x, y = nx, ny

s2 = eval_grid(new_grid, '[')

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)