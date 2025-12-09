import lib.aoc
import lib.graph
import lib.grid


def part1(s):
    grid = lib.grid.FixedGrid.parse(s)
    start = grid.find('S')
    grid[start] = '.'

    positions = [start]
    for i in range(64):
        next_positions = set()
        for p in positions:
            next_positions.update(grid.neighbors(*p))

        positions = [p for p in next_positions if grid[p] != '#']

    answer = len(positions)

    lib.aoc.give_answer_current(1, answer)


def part2(s):
    grid = lib.grid.FixedGrid.parse(s)
    start = grid.find('S')
    grid[start] = '.'

    positions = [start]

    assert start[0] == start[1]
    assert grid.width == grid.height

    for i in range(start[0] + grid.width * 2):
        next_positions = set()

        for x, y in positions:
            for n in [(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)]:
                next_positions.add(n)
        positions = [(nx, ny) for nx, ny in next_positions if grid[nx % grid.width, ny % grid.height] != '#']

    d = grid.width
    distance_to_corner = sum(start)
    steps = 26501365

    rem = steps % d
    times = steps // d

    corners = 0
    supercorners = 0
    odds = 0
    evens = 0

    for x in range(-times, times + 1):
        y_d = times - abs(x)
        if y_d > 0:
            height = y_d * 2 + 1
            if x != 0:
                corners += 2
            height -= 2
            evens += height // 2
            odds += height // 2 + 1
        if x != 0:
            supercorners += 2

    corners //= 4
    supercorners //= 4

    even_count = 0
    odd_count = 0
    top_count = 0
    bottom_count = 0
    left_count = 0
    right_count = 0
    ul_corner = 0
    ur_corner = 0
    bl_corner = 0
    br_corner = 0

    uul, uur, bbl, bbr = 0, 0, 0, 0

    for x, y in positions:
        if 0 <= x < grid.width:
            if 0 <= y < grid.height:
                even_count += 1
            elif grid.height <= y < 2 * grid.height:
                odd_count += 1
            elif 2 * grid.height <= y < 3 * grid.height:
                top_count += 1
            elif -grid.height > y >= -2 * grid.height:
                bottom_count += 1
        elif grid.width <= x < 2 * grid.width:
            if grid.height <= y < 2 * grid.height:
                ur_corner += 1
            elif 0 > y >= -grid.height:
                br_corner += 1
            elif -grid.height > y >= -2 * grid.height:
                bbr += 1
            elif 2 * grid.height <= y < 3 * grid.height:
                uur += 1
        elif 2 * grid.width <= x < 3 * grid.width:
            if 0 <= y < grid.height:
                right_count += 1
        elif 0 > x >= -grid.width:
            if grid.height <= y < 2 * grid.height:
                ul_corner += 1
            elif 0 > y >= -grid.height:
                bl_corner += 1
            elif -grid.height > y >= -2 * grid.height:
                bbl += 1
            elif 2 * grid.height <= y < 3 * grid.height:
                uul += 1
        elif -grid.width > x >= -2 * grid.width:
            if 0 <= y < grid.height:
                left_count += 1

    answer = 0
    answer += evens * even_count
    answer += odds * odd_count
    answer += top_count
    answer += bottom_count
    answer += left_count
    answer += right_count
    answer += corners * ul_corner
    answer += corners * ur_corner
    answer += corners * bl_corner
    answer += corners * br_corner

    answer += supercorners * uur
    answer += supercorners * uul
    answer += supercorners * bbr
    answer += supercorners * bbl

    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
