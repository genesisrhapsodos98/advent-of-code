import networkx as nx

import lib.aoc
import lib.graph
import lib.grid


def parse_input(s):
    lines = s.splitlines()

    computers = nx.Graph()
    for line in lines:
        left, right = line.split('-')
        computers.add_edge(left, right)
    computers = computers.to_undirected()

    return computers


def part1(s):
    computers = parse_input(s)
    cycles = nx.simple_cycles(computers, length_bound=3)
    valid_cycles = [cycle for cycle in cycles if len(cycle) == 3 and any([edge.startswith('t') for edge in cycle])]
    answer = len(valid_cycles)

    lib.aoc.give_answer_current(1, answer)


def part2(s):
    computers = parse_input(s)
    all_cliques = list(nx.enumerate_all_cliques(computers))
    sorted_computers = sorted(all_cliques[-1])
    answer = ','.join(sorted_computers)
    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
