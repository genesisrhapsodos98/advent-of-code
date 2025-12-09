import itertools
import lib.aoc
from shapely.geometry import Polygon
from shapely.prepared import prep

def parse_input(s: str):
    points = []
    for line in s.splitlines():
        line = line.strip()
        if not line:
            continue
        x_str, y_str = line.split(',')
        points.append((int(x_str), int(y_str)))
    return points

def solve(points, inscribed=False):
    polygon = Polygon(points)
    prepared_polygon = prep(polygon)
    best_area = 0

    for (x1, y1), (x2, y2) in itertools.combinations(points, 2):
        min_x, max_x = min(x1, x2), max(x1, x2)
        min_y, max_y = min(y1, y2), max(y1, y2)
        rect = Polygon([(min_x, min_y), (max_x, min_y), (max_x, max_y), (min_x, max_y)])
        if not inscribed or prepared_polygon.covers(rect):
            best_area = max(best_area, (max_x - min_x + 1) * (max_y - min_y + 1))
    return best_area

def part1(s: str):
    points = parse_input(s)
    answer = solve(points)

    lib.aoc.give_answer_current(1, answer)

def part2(s: str):
    points = parse_input(s)
    answer = solve(points, True)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
