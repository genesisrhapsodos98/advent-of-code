from itertools import product
from typing import List, Tuple

import networkx as nx

import lib.aoc
import lib.graph
import lib.grid


def read_map(s: str) -> List[List[str]]:
    return [list(line.strip()) for line in s.splitlines()]


Point = Tuple[int, int]


def find_start_end(grid: List[List[str]]) -> Tuple[Point, Point]:
    start: Point = (-1, -1)
    end: Point = (-1, -1)
    for i in range(len(grid)):
        for j in range(len(grid[0])):
            if grid[i][j] == 'S':
                start = (i, j)
            elif grid[i][j] == 'E':
                end = (i, j)
    if start == (-1, -1) or end == (-1, -1):
        raise ValueError("Start or end position not found in grid")
    return start, end


def build_graph(grid: List[List[str]], allow_walls: bool = False) -> nx.Graph:
    """Build a graph representation of the grid."""
    G = nx.Graph()
    height, width = len(grid), len(grid[0])
    directions = [(0, 1), (1, 0), (0, -1), (-1, 0)]

    for y, x in product(range(height), range(width)):
        if not allow_walls and grid[y][x] == '#':
            continue
        pos = (y, x)
        for dy, dx in directions:
            new_y, new_x = y + dy, x + dx
            if (0 <= new_y < height and
                    0 <= new_x < width and
                    (allow_walls or grid[new_y][new_x] in '.SE')):
                G.add_edge(pos, (new_y, new_x), weight=1)

    return G


def find_all_cheats(grid: List[List[str]], start: Point, end: Point, max_cheat_steps: int) -> List[int]:
    print("Building normal graph and finding shortest path...")
    G = build_graph(grid)
    try:
        normal_time = nx.shortest_path_length(G, start, end, weight='weight')
    except nx.NetworkXNoPath:
        return []
    print(f"Normal path length: {normal_time}")

    # Build graph that includes wall passages
    print("Building graph with wall passages...")
    G_walls = build_graph(grid, allow_walls=True)

    # Pre-calculate all shortest paths from start and to end
    print("Pre-calculating distances...")
    start_distances = nx.single_source_dijkstra_path_length(G, start, weight='weight')
    end_distances = nx.single_source_dijkstra_path_length(G, end, weight='weight')

    saved_times = []
    height, width = len(grid), len(grid[0])
    max_end_dist = normal_time - 100  # Maximum distance from cheat end to end

    print("Finding cheats...")
    # For each valid path position
    for y, x in product(range(height), range(width)):
        if grid[y][x] not in '.SE':
            continue
        start_pos = (y, x)
        if start_pos not in start_distances:
            continue

        start_dist = start_distances[start_pos]

        # Find all reachable positions within max_cheat_steps
        cheat_ends = nx.single_source_dijkstra_path_length(G_walls, start_pos, cutoff=max_cheat_steps)

        # Check each possible cheat end
        for end_pos, cheat_steps in cheat_ends.items():
            if grid[end_pos[0]][end_pos[1]] not in '.SE':
                continue
            if end_pos not in end_distances:
                continue

            end_dist = end_distances[end_pos]
            if end_dist > max_end_dist:
                continue

            # Calculate total time with cheat
            cheat_time = start_dist + cheat_steps + end_dist
            time_saved = normal_time - cheat_time

            if time_saved >= 100:
                saved_times.append(time_saved)

    print(f"Found {len(saved_times)} cheats that save ≥100 picoseconds")
    return saved_times


def part1(s: str):
    grid = read_map(s)
    start, end = find_start_end(grid)
    saved_times = find_all_cheats(grid, start, end, max_cheat_steps=2)
    lib.aoc.give_answer_current(1, len(saved_times))


def part2(s: str):
    grid = read_map(s)
    start, end = find_start_end(grid)
    saved_times = find_all_cheats(grid, start, end, max_cheat_steps=20)
    lib.aoc.give_answer_current(2, len(saved_times))


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
