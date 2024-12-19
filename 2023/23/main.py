import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid

slopes = {
    '>': (1, 0),
    'v': (0, 1),
    '<': (-1, 0),
    '^': (0, -1),
}

def part1(s):
    grid = lib.grid.FixedGrid.parse(s)
    start_pos = (1, 0)
    end_pos = (grid.width - 2, grid.height - 1)

    def neighbor_fn(coord):
        x, y = coord
        handled = {coord}
        queue = [(n, 1) for n in grid.neighbors(*coord) if grid[n] != '#']

        while queue:
            coord, d = queue.pop()

            handled.add(coord)

            if coord == end_pos:
                yield coord, d
                continue
            if grid[coord] in slopes:
                dx, dy = slopes[grid[coord]]
                n = (x + dx, y + dy)
                if n not in handled:
                    queue.append((n, d + 1))
                continue
            else:
                assert grid[coord] == '.'

            neighbors = [n for n in grid.neighbors(*coord) if grid[n] != '#']
            if len(neighbors) > 2:
                yield coord, d
                continue

            neighbors = [n for n in neighbors if n not in handled]

            if len(neighbors) == 0:
                continue

            n = neighbors[0]
            queue.append((n, d + 1))

    def longest_path(path, end, dist):
        best = -1
        for n, n_dist in graph[path[-1]]:
            if n in path:
                continue
            if n == end:
                best = max(best, dist + n_dist)
                continue

            best = max(best, longest_path(path + (n,), end, dist + n_dist))

        return best

    graph = lib.graph.make_lazy_graph(neighbor_fn)
    answer = longest_path((start_pos,), end_pos, 0)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    grid = lib.grid.FixedGrid.parse(s.replace('^', '.').replace('>', '.').replace('v', '.').replace('<^>', '.'))
    start_pos = (1, 0)
    end_pos = (grid.width - 2, grid.height - 1)

    def neighbor_fn(coord):
        x, y = coord
        handled = {coord}
        queue = [(n, 1) for n in grid.neighbors(*coord) if grid[n] != '#']

        while queue:
            coord, d = queue.pop()

            handled.add(coord)

            if coord == end_pos:
                yield coord, d
                continue
            if grid[coord] in slopes:
                dx, dy = slopes[grid[coord]]
                n = (x + dx, y + dy)
                if n not in handled:
                    queue.append((n, d + 1))
                continue

            neighbors = [n for n in grid.neighbors(*coord) if grid[n] != '#']
            if len(neighbors) > 2:
                yield coord, d
                continue

            if len(neighbors) == 2:
                continue

            n = neighbors[0]
            queue.append((n, d + 1))

    def longest_path(path, end, dist):
        best = -1
        for n, n_dist in graph[path[-1]]:
            if n in path:
                continue
            if n == end:
                best = max(best, dist + n_dist)
                continue

            best = max(best, longest_path(path + (n,), end, dist + n_dist))

        return best

    graph = lib.graph.make_lazy_graph(neighbor_fn)
    answer = longest_path((start_pos,), end_pos, 0)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INP