import functools

import lib.aoc
import lib.graph
import lib.grid


@functools.cache
def count_reachable(d, patterns):
    if d == '':
        return 1
    matches = [p for p in patterns if d.startswith(p)]
    if len(matches) == 0:
        return 0
    reachable_states = sum([count_reachable(d[len(match):], patterns) for match in matches])
    return reachable_states


def parse_input(s):
    top, bottom = s.split('\n\n')
    patterns = frozenset(top.split(', '))
    designs = frozenset(bottom.splitlines())
    return patterns, designs


def part1(s):
    patterns, designs = parse_input(s)

    answer = 0
    for design in designs:
        if count_reachable(design, patterns) > 0:
            answer += 1

    lib.aoc.give_answer_current(1, answer)


def part2(s):
    patterns, designs = parse_input(s)

    answer = 0
    for design in designs:
        answer += count_reachable(design, patterns)
    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
