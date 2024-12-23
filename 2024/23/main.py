import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid
from lib.graphics import *
import networkx as nx

def parse_input(s):
    lines = s.splitlines()
    pairs = []
    for line in lines:
        a, b = line.split('-')
        pairs.append((a, b))
    return pairs

def part1(s):
    pairs = parse_input(s)
    graph = nx.Graph()
    for pair in pairs:
        left, right = pair
        graph.add_edge(left, right)
    graph = graph.to_undirected()
    cycles = nx.simple_cycles(graph, length_bound=3)
    valid_cycles = [cycle for cycle in cycles if len(cycle) == 3 and any([edge.startswith('t') for edge in cycle])]
    answer = len(valid_cycles)
    valid_cycles_set = set([tuple(cycle) for cycle in valid_cycles])
    answer_2 = len(valid_cycles_set)
    print(answer)
    print(answer_2)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
    _ = parse_input(s)
    answer = 0
    # lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
