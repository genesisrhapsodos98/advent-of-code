import collections
import functools
import itertools
import math
import re
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

    on_best_path = set()

    best_seen = {}
    known_retvals = {}

    def impl(state, cost):
        retval = known_retvals.get((state, cost))
        if retval is not None:
            return retval

        if cost > min_length:
            known_retvals[state, cost] = False
            return False

        if best_seen.get(state, cost) < cost:
            known_retvals[state, cost] = False
            return False

        best_seen[state] = cost

        if end_fn(state):
            assert(cost == min_length)
            on_best_path.add(state[0])
            known_retvals[state, cost] = True
            return True

        if cost == min_length:
            known_retvals[state, cost] = False
            return False

        is_good = False

        for neighbor, n_cost in graph[state]:
            if impl(neighbor, cost + n_cost):
                on_best_path.add(state[0])
                is_good = True

        known_retvals[state, cost] = is_good
        return is_good

    impl((start, start_dir), 0)

    answer = len(on_best_path)

    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
