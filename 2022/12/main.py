import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid
from lib.graphics import *

def parse_input(s):
    grid = lib.grid.FixedGrid.parse(s)
    return grid
def resolve_elevation(e):
    if (e == 'S'):
        return 'a'
    elif (e == 'E'):
        return 'z'
    else:
        return e

def part1(s):
    grid = parse_input(s)
    def neighbor_fn(pos):
        start_elevation = resolve_elevation(grid[pos])
        for n in grid.neighbors(*pos):
            end_elevation = resolve_elevation(grid[n])
            if ord(end_elevation) - ord(start_elevation) > 1:
                continue
            yield n, 1
    graph = lib.graph.make_lazy_graph(neighbor_fn)
    start = grid.find('S')
    end = grid.find('E')
    answer = lib.graph.dijkstra_length(graph, start, end)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    grid = parse_input(s)

    def neighbor_fn(pos):
        start_elevation = resolve_elevation(grid[pos])
        for n in grid.neighbors(*pos):
            end_elevation = resolve_elevation(grid[n])
            if ord(end_elevation) - ord(start_elevation) > 1:
                continue
            yield n, 1

    graph = lib.graph.make_lazy_graph(neighbor_fn)
    coords_by_value = grid.coords_by_value()
    start = coords_by_value['a'] + coords_by_value['S']
    end = grid.find('E')
    answer = lib.graph.dijkstra_length(graph, start, end)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
