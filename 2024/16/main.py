import lib.aoc
import lib.graph
import lib.grid


def part1(s):
    grid = lib.grid.FixedGrid.parse(s)
    start = grid.find('S')
    ex, ey = grid.find('E')
    start_dir = (1, 0)

    def neighbor_fn(state):
        (x, y), (dx, dy) = state
        neighbors = []
        nx, ny = x + dx, y + dy
        if (nx, ny) in grid and grid[nx, ny] != '#':
            neighbors.append((((nx, ny), (dx, dy)), 1))

        # Rotate left
        ldx, ldy = dy, dx
        neighbors.append((((x, y), (ldx, ldy)), 1000))
        # Rotate right
        rdx, rdy = -dy, -dx
        neighbors.append((((x, y), (rdx, rdy)), 1000))

        return neighbors

    def end_fn(state):
        (x, y), (_, _) = state
        return x == ex and y == ey

    graph = lib.graph.make_lazy_graph(neighbor_fn)

    answer = lib.graph.dijkstra_length_fuzzy_end(graph, (start, start_dir), end_fn)

    lib.aoc.give_answer_current(1, answer)


def part2(s):
    grid = lib.grid.FixedGrid.parse(s)
    start = grid.find('S')
    ex, ey = grid.find('E')
    start_dir = (1, 0)

    def neighbor_fn(state):
        (x, y), (dx, dy) = state
        neighbors = []
        nx, ny = x + dx, y + dy
        if (nx, ny) in grid and grid[nx, ny] != '#':
            neighbors.append((((nx, ny), (dx, dy)), 1))

        # Rotate left
        ldx, ldy = dy, dx
        neighbors.append((((x, y), (ldx, ldy)), 1000))
        # Rotate right
        rdx, rdy = -dy, -dx
        neighbors.append((((x, y), (rdx, rdy)), 1000))

        return neighbors

    def end_fn(state):
        (x, y), (_, _) = state
        return x == ex and y == ey

    graph = lib.graph.make_lazy_graph(neighbor_fn)

    min_length = lib.graph.dijkstra_length_fuzzy_end(graph, (start, start_dir), end_fn)

    best_path_positions = set()

    best_cost = {}
    result_cache = {}

    def walk_best_path(state, cost):
        result = result_cache.get((state, cost))
        if result is not None:
            return result

        if cost > min_length:
            result_cache[state, cost] = False
            return False

        if best_cost.get(state, cost) < cost:
            result_cache[state, cost] = False
            return False

        best_cost[state] = cost

        if end_fn(state):
            assert (cost == min_length)
            best_path_positions.add(state[0])
            result_cache[state, cost] = True
            return True

        if cost == min_length:
            result_cache[state, cost] = False
            return False

        is_on_best_path = False

        for neighbor, n_cost in graph[state]:
            if walk_best_path(neighbor, cost + n_cost):
                best_path_positions.add(state[0])
                is_on_best_path = True

        result_cache[state, cost] = is_on_best_path
        return is_on_best_path

    walk_best_path((start, start_dir), 0)

    answer = len(best_path_positions)
    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
