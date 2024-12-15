import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
input_content = \
"""2413432311323
3215453535623
3255245654254
3446585845452
4546657867536
1438598798454
4457876987766
3637877979653
4654967986887
4564679986453
1224686865563
2546548887735
4322674655533"""
grid = FixedGrid.parse(input_content, value_fn=int)

def custom_dfs(pos, dir, dir_count, path, value, visited):
    x, y = pos
    dx, dy = dir

    if (x, y) == (grid.width -1, grid.height - 1):
        return path, value


    next_nodes = grid.neighbors(x, y)
    # Remove visited
    next_nodes = [node for node in next_nodes if node not in visited]
    # Remove backwards
    next_nodes = [node for node in next_nodes if node != (x - dx, y - dy)]
    # Remove 4-length paths
    next_nodes = [node for node in next_nodes if node != (x + dx, y + dy) or dir_count == 3]

    next_values = []
    for node in next_nodes:
        nx, ny = node
        ndx, ndy = nx - x, ny - y
        new_dir_count = 0 if (ndx, ndy) != (dx, dy) else dir_count + 1
        new_path = path
        new_path.append(node)
        visited.add(node)
        new_value = value + grid[node]
        next_values.append(custom_dfs((nx, ny), (ndx, ndy), new_dir_count, new_path, new_value, visited))

s = 0
s2 = 0

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)