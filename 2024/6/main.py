input_file = open(".\\input.txt", "r")
input_content = input_file.read()
lines = input_content.split('\n')

visited = {}
guard_position = (0, 0)

map_height = len(lines)
map_width = len(lines[0])

directions = [(0, -1), (1, 0), (0, 1), (-1, 0)]
guard_direction = directions[0]


def in_bounds(coords):
    x, y = coords
    return 0 <= x < map_width and 0 <= y < map_height


def add_coordinates(coords, offset):
    x, y = coords
    ox, oy = offset
    return (x + ox, y + oy)


neighbor = dict()
blocks = set()
nodes = [(x, y, d) for x in range(map_width) for y in range(map_height) for d in range(4)]

for x, y in [(x, y) for x in range(map_width) for y in range(map_height)]:
    if lines[y][x] == '#':
        blocks.add((x, y))
    elif lines[y][x] == '^':
        start_pos = (x, y, 0)

for x, y, d in nodes:
    new_neighbor = add_coordinates((x, y), directions[d])
    if not in_bounds(new_neighbor):
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

neighbor = [[[(x, y, d) for d in range(4)] for y in range(map_height)] for x in range(map_width)]
blocks = [[False for y in range(map_height)] for x in range(map_width)]
nodes = [(x, y, d) for x in range(map_width) for y in range(map_height) for d in range(4)]

s = len(original_visited)
s2 = len(loop_obstacles)

print(s)
print(s2)
