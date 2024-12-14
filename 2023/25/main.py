import networkx
from networkx import capacity_scaling

import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

lefts = []
rights = []

for line in lines:
    [l, r] = line.split(':')
    rx = r.strip().split()
    lefts.append(l)
    rights.append(rx)

s = 0

graph = networkx.Graph()

for src, dsts in zip(lefts, rights):
    for dst in dsts:
        graph.add_edge(src, dst, capacity = 1)

nodes = list(graph)

found_cuts = False
for idx, node in enumerate(nodes):
    if found_cuts:
        break

    for next_node in nodes[idx + 1:]:
        cuts, (left, right) = networkx.minimum_cut(graph, node, next_node)
        if cuts == 3:
            s += len(left) * len(right)
            found_cuts = True
            break

lib.aoc.give_answer_current(1, s)