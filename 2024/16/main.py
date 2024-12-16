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
    pass
##    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
