import collections
import functools

import lib.aoc

def parse_input(s: str):
    graph = {}
    for line in s.splitlines():
        line = line.strip()
        if not line:
            continue
        left, right = line.split(":")
        src = left.strip()
        dests = right.strip()
        if dests:
            neighbors = dests.split()
        else:
            neighbors = []
        graph[src] = neighbors
    return graph


def count_paths(graph, start, end, must_visit=None):
    if must_visit is None:
        must_visit = []
    must_visit = set(must_visit)

    # DFS with state memoization using a bitmask to track all visited nodes in list of must_visit nodes
    @functools.cache
    def dfs(node, visited_mask):
        if node == end:
            return 1 if visited_mask == (1 << len(must_visit)) - 1 else 0

        next_mask = visited_mask
        for idx, name in enumerate(must_visit):
            if node == name:
                next_mask |= (1 << idx)

        total = 0
        for nxt in graph.get(node, []):
            total += dfs(nxt, next_mask)

        return total

    return dfs(start, 0)


def part1(s: str):
    graph = parse_input(s)
    answer = count_paths(graph, "you", "out")
    lib.aoc.give_answer_current(1, answer)


def part2(s: str):
    graph = parse_input(s)
    answer = count_paths(graph, "svr", "out", ["dac", "fft"])
    lib.aoc.give_answer_current(2, answer)
    

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
