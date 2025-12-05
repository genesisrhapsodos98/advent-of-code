# z3.If(x >= 0, x, -x); z3.And(); z3.Or(); z3.Not()
# s = z3.Solver(); solver.add(constraint); s.check(); s.model()[x].as_long()
# o = z3.Optimize(); o.minimize(x); o.check(); o.model()[x].as_long()

import lib.algorithms
import lib.aoc
import lib.cyk
import lib.graph
import lib.grid
import lib.hex_coord
import lib.lazy_dict
import lib.math
import lib.ocr
import lib.parsing

def parse_input(s):
    sections = s.strip().split('\n\n')

    fresh_ranges = []
    for line in sections[0].splitlines():
        start, end = map(int, line.split('-'))
        fresh_ranges.append((start, end))

    available_ids = [int(x) for x in sections[1].splitlines()]

    return fresh_ranges, available_ids


def merge_ranges(ranges):
    ranges = sorted(ranges, key=lambda x: x[0])
    merged = []

    for start, end in ranges:
        if not merged or start > merged[-1][1] + 1:
            merged.append([start, end])
        else:
            merged[-1][1] = max(merged[-1][1], end)

    return merged

def part1(s):
    fresh_ranges, available_ids = parse_input(s)

    fresh_count = 0
    for ing_id in available_ids:
        if any(start <= ing_id <= end for start, end in fresh_ranges):
            fresh_count += 1

    lib.aoc.give_answer_current(1, fresh_count)


def part2(s):
    fresh_ranges, _ = parse_input(s)

    merged = merge_ranges(fresh_ranges)

    total_fresh = sum(end - start + 1 for start, end in merged)

    lib.aoc.give_answer_current(2, total_fresh)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
