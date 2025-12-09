from functools import lru_cache

import networkx as nx
import re2 as re
import lib.aoc

def parse_input(s):
    G = nx.Graph()
    flow = {}

    for line in s.splitlines():
        m = re.match(r"Valve (\w+) has flow rate=(\d+); tunnels? leads? to valves? (.*)", line)
        valve = m.group(1)
        rate = int(m.group(2))
        targets = [x.strip() for x in m.group(3).split(",")]

        flow[valve] = rate
        for t in targets:
            G.add_edge(valve, t)

    return G, flow

def part1(s):
    G, flow = parse_input(s)

    useful = ["AA"] + [v for v, r in flow.items() if r > 0]

    dist = {u: {} for u in useful}
    for u in useful:
        lengths = nx.shortest_path_length(G, source=u)
        for v in useful:
            if v in lengths:
                dist[u][v] = lengths[v]

    flow_valves = [v for v in useful if flow[v] > 0]
    idx = {v: i for i, v in enumerate(flow_valves)}
    N = len(flow_valves)

    from functools import lru_cache

    @lru_cache(None)
    def dfs(cur, time_left, opened_mask):
        best = 0
        for v in flow_valves:
            bit = 1 << idx[v]
            if opened_mask & bit:
                continue

            travel = dist[cur][v]
            time_after_open = time_left - travel - 1
            if time_after_open <= 0:
                continue

            gain = flow[v] * time_after_open
            best = max(best,
                       gain + dfs(v, time_after_open, opened_mask | bit))
        return best

    answer = dfs("AA", 30, 0)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    G, flow = parse_input(s)

    useful = ["AA"] + [v for v, r in flow.items() if r > 0]

    dist = {u: {} for u in useful}
    for u in useful:
        lengths = nx.shortest_path_length(G, source=u)
        for v in useful:
            if v in lengths:
                dist[u][v] = lengths[v]

    flow_valves = [v for v in useful if flow[v] > 0]
    idx = {v: i for i, v in enumerate(flow_valves)}
    N = len(flow_valves)

    @lru_cache(None)
    def dfs(cur, time_left, opened_mask):
        best = 0
        for v in flow_valves:
            bit = 1 << idx[v]
            if not (opened_mask & bit):
                continue

            travel = dist[cur][v]
            t_after = time_left - travel - 1
            if t_after <= 0:
                continue

            gain = flow[v] * t_after
            best = max(best, gain + dfs(v, t_after, opened_mask ^ bit))
        return best

    best = {}
    fullmask = (1 << N) - 1
    TIME = 26

    for mask in range(fullmask + 1):
        best[mask] = dfs("AA", TIME, mask)

    answer = 0
    for mask in range(fullmask + 1):
        elephant_mask = fullmask ^ mask
        answer = max(answer, best[mask] + best[elephant_mask])
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
