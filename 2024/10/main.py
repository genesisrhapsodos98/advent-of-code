import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
grid = FixedGrid.parse(input_content, value_fn=int)

lines = input_content.split('\n')

trail_heads = []

def dfs(coords, trail, summits, distinct):
    x, y = coords
    value = grid[coords]

    if value == 9 and (coords not in summits or distinct is True):
        summits.append(coords)
        # print(f'Found trail: {trail}')
        return 1

    adjacent_neighbors = grid.neighbors(x, y)
    adjacent_nodes = [neighbor for neighbor in adjacent_neighbors if grid[neighbor] == value + 1]

    result = 0
    for node in adjacent_nodes:
        result += dfs(node, trail + [node], summits, distinct)

    return result

def score_trail_head(trail_head, distinct):
    return dfs(trail_head, [trail_head], [], distinct)

for coords, v in grid.items():
    if v == 0:
        trail_heads.append(coords)

s = 0
s2 = 0

for trail_head in trail_heads:
    score = score_trail_head(trail_head, False)
    rating = score_trail_head(trail_head, True)
    s += score
    s2 += rating

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)