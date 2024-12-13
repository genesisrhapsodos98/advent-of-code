import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

map_height = len(lines)
map_width = len(lines[0])

trail_heads = []

def in_bounds(coords):
    x, y = coords
    return 0 <= x < map_width and 0 <= y < map_height

def get_value(coords):
    x, y = coords
    return int(lines[y][x])

def dfs(coords, trail, summits, distinct):
    x, y = coords
    value = get_value(coords)

    if value == 9 and (coords not in summits or distinct is True):
        summits.append(coords)
        # print(f'Found trail: {trail}')
        return 1

    adjacent_coords = [(x+1, y), (x-1, y), (x, y+1), (x, y-1)]
    adjacent_nodes = [c for c in adjacent_coords if in_bounds(c) and get_value(c) == value + 1]

    result = 0
    for node in adjacent_nodes:
        result += dfs(node, trail + [node], summits, distinct)

    return result

def score_trail_head(trail_head, distinct):
    return dfs(trail_head, [trail_head], [], distinct)


for i in range(map_height):
    for j in range(map_width):
        if get_value((j, i)) == 0:
            trail_heads.append((j, i))

s = 0
s2 = 0

for trail_head in trail_heads:
    score = score_trail_head(trail_head, False)
    rating = score_trail_head(trail_head, True)
    s += score
    s2 += rating

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)