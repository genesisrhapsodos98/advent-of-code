import lib.aoc
import lib.graph
import lib.grid

slopes = {
    '>': (1, 0),
    'v': (0, 1),
    '<': (-1, 0),
    '^': (0, -1),
}


def solve(grid):
    start_pos = (grid.row(0).index('.'), 0)
    end_pos = (grid.row(grid.height - 1).index('.'), grid.height - 1)

    def neighbor_fn(coord):
        handled = {coord}
        queue = [(n, 1) for n in grid.neighbors(*coord) if grid[n] != '#']

        while queue:
            coord, d = queue.pop()

            handled.add(coord)

            if coord == end_pos:
                yield coord, d
                continue
            if grid[coord] in slopes:
                x, y = coord
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
    return answer


def part1(s):
    grid = lib.grid.FixedGrid.parse(s)
    answer = solve(grid)
    lib.aoc.give_answer_current(1, answer)


def part2(s):
    grid = lib.grid.FixedGrid.parse(s.replace('^', '.').replace('>', '.').replace('v', '.').replace('<^>', '.'))
    answer = solve(grid)
    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
