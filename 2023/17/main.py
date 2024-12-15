import lib.aoc
from lib.graph import make_lazy_graph, all_reachable, dijkstra_length_fuzzy_end
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
grid = FixedGrid.parse(input_content, value_fn=int)

graph = {}
for coord, value in grid.items():
    x, y = coord
    neighbors = grid.neighbors(x, y)
    graph[coord] = [(n_coord, grid[n_coord]) for n_coord in neighbors]

def generate_heuristic_to_end_node(grid: FixedGrid):
    def heuristic_neighbor(state):
        x, y = state
        for n in grid.neighbors(x, y):
            yield n, grid[x, y]

    heuristic_graph = make_lazy_graph(heuristic_neighbor)

    heuristic = dict(all_reachable(heuristic_graph,
                                             (grid.width-1,
                                              grid.height-1)))
    heuristic[grid.width-1, grid.height-1] = 0
    return heuristic.__getitem__

def solve(grid: FixedGrid, min_steps = 0, max_steps = 3):
    w, h = grid.width, grid.height

    def neighbor_fn(state):
        x, y, horizontal = state
        if horizontal:
            for ndy in (1, -1):
                ny = y
                cost = 0
                for steps in range(1, max_steps + 1):
                    ny += ndy
                    if 0 <= ny < h:
                        cost += grid[x, ny]
                        if steps >= min_steps:
                            new_state = (x, ny, False)
                            yield new_state, cost
                    else:
                        break
        else:
            for ndx in (1, -1):
                nx = x
                cost = 0
                for steps in range(1, max_steps + 1):
                    nx += ndx
                    if 0 <= nx < w:
                        cost += grid[nx, y]
                        if steps >= min_steps:
                            new_state = (nx, y, True)
                            yield new_state, cost

    def end_fn(state):
        x, y, _ = state
        return x == w - 1 and y == h - 1

    graph = make_lazy_graph(neighbor_fn)
    heuristic_to_end = generate_heuristic_to_end_node(grid)

    def heuristic(state):
        x, y, _ = state
        return heuristic_to_end((x, y))

    return dijkstra_length_fuzzy_end(graph, [(0, 0, True), (0, 0, False)], end_fn, heuristic)


s = solve(grid)
s2 = solve(grid, 4, 10)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)