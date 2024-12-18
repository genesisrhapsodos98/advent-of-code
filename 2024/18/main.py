import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid

def parse_input(s, lim=0):
    lines = s.splitlines()
    d = dict()
    d[(0, 0)] = '.'
    for idx, line in enumerate(lines):
        if idx == lim:
            break
        x, y = list(map(int, line.split(',')))
        d[(x, y)] = '#'
    grid = lib.grid.FixedGrid.from_dict(d, missing='.')
    grid.print(line_spacing='')
    return grid

def shortest_length(grid: lib.grid.FixedGrid):
    start = (0, 0)
    end = (grid.width - 1, grid.height - 1)

    def neighbor_fn(coord):
        x, y = coord
        neighbors = []
        for n in grid.neighbors(x, y):
            if grid[n] != '#':
                neighbors.append((n, 1))

        return neighbors

    graph = lib.graph.make_lazy_graph(neighbor_fn)
    answer = lib.graph.dijkstra_length(graph, start, end)

    return answer

def part1(s):
    grid = parse_input(s, 1024)
    answer = shortest_length(grid)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
##    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
