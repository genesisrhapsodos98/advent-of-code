import lib.aoc
import lib.graph
import lib.grid


def parse_input(s, lim=0, size=70):
    lines = s.splitlines()
    d = dict()
    d[(0, 0)] = '.'
    d[(size, size)] = '.'
    for idx, line in enumerate(lines):
        if idx == lim:
            break
        x, y = list(map(int, line.split(',')))
        d[(x, y)] = '#'
    grid = lib.grid.FixedGrid.from_dict(d, missing='.')
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
    lines = s.splitlines()

    low, high = 0, len(lines)
    found = False
    # Binary search to find idx
    while not found:
        mid = (high + low) // 2
        grid_1 = parse_input(s, mid)
        grid_2 = parse_input(s, mid + 1)
        escape_path_1 = shortest_length(grid_1)
        escape_path_2 = shortest_length(grid_2)
        if escape_path_1 > 0 and escape_path_2 < 0:
            found = True
        else:
            if escape_path_2 > 0:
                low = mid
            elif escape_path_1 < 0:
                high = mid

    answer = lines[mid]

    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
