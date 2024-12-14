import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
grid = FixedGrid.parse(input_content)

visited = {}
guard_position = (0, 0)

directions = [(0, -1), (1, 0), (0, 1), (-1, 0)]
guard_direction = directions[0]

neighbor = dict()
blocks = set()
nodes = [(x, y, d) for x in grid.x_range for y in grid.y_range for d in range(4)]

start_x, start_y = grid.find('^')
start_pos = (start_x, start_y, 0)

grouped = grid.coords_by_value()
for coords in grouped['#']:
    blocks.add(coords)

for x, y, d in nodes:
    dx, dy = directions[d]
    new_neighbor = (x + dx, y + dy)
    if new_neighbor not in grid:
        neighbor[(x, y, d)] = (-1, -1, -1)
    elif new_neighbor in blocks:
        neighbor[(x, y, d)] = (x, y, (d + 1) % 4)
    else:
        neighbor[(x, y, d)] = (new_neighbor[0], new_neighbor[1], d)

original_path = []
original_visited = set()
pos = start_pos

while pos != (-1, -1, -1):
    original_path.append(pos)
    original_visited.add((pos[0], pos[1]))
    pos = neighbor[pos]

loop_obstacles = set()
non_loop_obstacles = set()

for idx, pos in enumerate(original_path[1:], 1):
    x, y, d = pos
    if (x, y) in loop_obstacles or (x, y) in non_loop_obstacles:
        continue
    for d in range(4):
        prev = (x - directions[d][0], y - directions[d][1], d)
        neighbor[prev] = (prev[0], prev[1], (d + 1) % 4)
    visited = set()
    current_node = original_path[idx - 1]
    while current_node != (-1, -1, -1) and current_node not in visited:
        visited.add(current_node)
        current_node = neighbor[current_node]
    if current_node == (-1, -1, -1):
        non_loop_obstacles.add((pos[0], pos[1]))
    else:
        loop_obstacles.add((pos[0], pos[1]))
    for d in range(4):
        prev = (x - directions[d][0], y - directions[d][1], d)
        neighbor[prev] = (pos[0], pos[1], d)

neighbor = [[[(x, y, d) for d in range(4)] for y in grid.y_range] for x in grid.x_range]
blocks = [[False for y in grid.y_range] for x in grid.x_range]
nodes = [(x, y, d) for x in grid.x_range for y in grid.y_range for d in range(4)]

s = len(original_visited)
s2 = len(loop_obstacles)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)
