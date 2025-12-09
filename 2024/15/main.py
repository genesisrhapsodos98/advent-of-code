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

moves = {
    '<': (-1, 0),
    '^': (0, -1),
    '>': (1, 0),
    'v': (0, 1)
}

def eval_grid(grid, box_elem='O'):
    boxes_pos = [coord for coord, value in grid.items() if value == box_elem]
    answer = 0
    for x, y in boxes_pos:
        answer += 100 * y + x
    return answer

def find_edge(boxes, direction):
    dx, dy = direction
    leftmost = min([x for x, y in boxes])
    rightmost = max([x for x, y in boxes])
    topmost = min([y for x, y in boxes])
    bottommost = max([y for x, y in boxes])

    if (dx, dy) == (1, 0):
        edge = set([pos for pos in boxes if pos[0] == rightmost])
    elif (dx, dy) == (-1, 0):
        edge = set([pos for pos in boxes if pos[0] == leftmost])
    elif (dx, dy) == (0, 1):
        edge = set([pos for pos in boxes if pos[1] == bottommost])
    else:
        edge = set([pos for pos in boxes if pos[1] == topmost])

    return edge

def solve_part_1(grid: FixedGrid, movements: str, start_pos):
    x, y = start_pos
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

    return eval_grid(grid)

def solve_part_2(grid: FixedGrid, movements: str, start_pos):
    x, y = start_pos
    for move in movements:
        dx, dy = moves[move]
        nx, ny = x + dx, y + dy

        if (nx, ny) not in grid or grid[nx, ny] == '#':
            continue

        if grid[nx, ny] == '.':
            x, y = nx, ny
            continue

        if grid[nx, ny] in '[]':
            boxes_pos = set()
            other_part = (nx - 1, ny) if grid[nx, ny] == ']' else (nx + 1, ny)
            boxes_pos.add((nx, ny))
            boxes_pos.add(other_part)

            edge_boxes = find_edge(boxes_pos, (dx, dy))

            can_move = True
            while len(edge_boxes) > 0:
                new_edge_boxes = set()
                for box in edge_boxes:
                    bx, by = box
                    px, py = bx + dx, by + dy

                    if grid[px, py] == '#':
                        new_edge_boxes = set()
                        can_move = False
                        break

                    if grid[px, py] in '[]':
                        other_part = (px - 1, py) if grid[px, py] == ']' else (px + 1, py)
                        new_edge_boxes.add((px, py))
                        new_edge_boxes.add(other_part)
                        boxes_pos.add((px, py))
                        boxes_pos.add(other_part)

                edge_boxes = new_edge_boxes
                if len(edge_boxes) == 0:
                    break

                edge_boxes = find_edge(edge_boxes, (dx, dy))

            if not can_move:
                continue

            replacements = []
            for bx, by in boxes_pos:
                elem = grid[bx, by]
                replacements.append(((bx + dx, by + dy), elem))
            for pos in boxes_pos:
                grid[pos] = '.'
            for pos, elem in replacements:
                grid[pos] = elem
            x, y = nx, ny
    return eval_grid(grid, '[')

robot_pos = grid.find("@")
grid[robot_pos] = '.'
s = solve_part_1(grid, movements, robot_pos)

new_robot_pos = new_grid.find('@')
new_grid[new_robot_pos] = '.'

s2 = solve_part_2(new_grid, movements, new_robot_pos)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)