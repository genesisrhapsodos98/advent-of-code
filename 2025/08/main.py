import collections

import lib.aoc

def parse_input(s: str):
    points = []
    for line in s.splitlines():
        line = line.strip()
        if not line:
            continue
        x, y, z = map(int, line.split(","))
        points.append((x, y, z))
    return points


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))
        self.size = [1] * n
        self.components = n

    def find(self, x: int) -> int:
        if x == self.parent[x]:
            return x
        p = self.find(self.parent[x])
        self.parent[x] = p
        return p

    def union(self, a: int, b: int) -> bool:
        ra = self.find(a)
        rb = self.find(b)
        if ra == rb:
            return False
        if self.size[ra] < self.size[rb]:
            ra, rb = rb, ra
        self.parent[rb] = ra
        self.size[ra] += self.size[rb]
        self.components -= 1
        return True

def build_dist_list(points):
    """Return list of (squared_distance, i, j) for all pairs, sorted by distance."""
    n = len(points)
    dists = []
    for i in range(n):
        x1, y1, z1 = points[i]
        for j in range(i + 1, n):
            x2, y2, z2 = points[j]
            dx = x1 - x2
            dy = y1 - y2
            dz = z1 - z2
            d2 = dx * dx + dy * dy + dz * dz
            dists.append((d2, i, j))
    dists.sort(key=lambda t: t[0])
    return dists

def solve(points, dists, num_pairs: int) -> int:
    n = len(points)
    dsu = DSU(n)

    # Connect the num_pairs closest pairs (even if already in same component)
    for k in range(min(num_pairs, len(dists))):
        _, i, j = dists[k]
        dsu.union(i, j)

    # Compute component sizes
    comp_sizes = collections.Counter()
    for i in range(n):
        root = dsu.find(i)
        comp_sizes[root] += 1

    # Get three largest circuit sizes
    largest = sorted(comp_sizes.values(), reverse=True)[:3]
    if len(largest) < 3:
        largest += [1] * (3 - len(largest))

    result = largest[0] * largest[1] * largest[2]
    return result


def part1(s: str):
    points = parse_input(s)
    dists = build_dist_list(points)
    answer = solve(points, dists, num_pairs=1000)
    lib.aoc.give_answer_current(1, answer)

def solve_part2(points, dists) -> int:
    n = len(points)
    dsu = DSU(n)

    last_pair = None

    # Now connect pairs in order of increasing distance, but only when they
    # are still in different components. Stop when everything is connected.
    for _, i, j in dists:
        if dsu.union(i, j):
            last_pair = (i, j)
            if dsu.components == 1:
                break

    # Multiply X coordinates of the last connected pair
    if last_pair is None:
        return 0  # Degenerate case (e.g., 0 or 1 point)

    i, j = last_pair
    x1, _, _ = points[i]
    x2, _, _ = points[j]
    return x1 * x2

def part2(s):
    points = parse_input(s)
    dists = build_dist_list(points)
    answer = solve_part2(points, dists)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
