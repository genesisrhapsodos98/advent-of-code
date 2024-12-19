import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid

def parse_input(s):
    top, bottom = s.split('\n\n')
    patterns = top.split(', ')

    designs = bottom.splitlines()
    return patterns, designs

def part1(s):
    patterns, designs = parse_input(s)

    count = 0
    for design in designs:
        initial_state = design
        queue = [initial_state]
        possible = False
        visited = set()
        while queue:
            d = queue.pop()
            if d == '':
                possible = True
                break
            matches = [p for p in patterns if d.startswith(p)]
            if len(matches) == 0:
                continue
            for match in matches:
                new_state = d[len(match):]
                if new_state in visited:
                    continue
                else:
                    visited.add(new_state)
                queue.append(new_state)
        if possible:
            count += 1

    ## nums = list(map(lambda r:r[0], parse.findall('{:d}', s)))
    # lines = s.splitlines()
    # groups = s.split('\n\n')
    # grid = lib.grid.FixedGrid.parse(s, value_fn=int)
    # grid = lib.grid.FixedGrid.parse(s,
    #                                linesplit_fn=lambda line: line.split(),
    #                                value_fn=int)
    answer = count
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    patterns, designs = parse_input(s)

    visited = dict()

    @functools.cache
    def count_reachable(d):
        if d in visited:
            return visited[d]
        if d == '':
            return 1
        matches = [p for p in patterns if d.startswith(p)]
        if len(matches) == 0:
            return 0
        reachable_states = sum([count_reachable(d[len(match):]) for match in matches])
        visited[d] = reachable_states
        return reachable_states

    answer = 0
    for design in designs:
        answer += count_reachable(design)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()

# INPUT = '''r, wr, b, g, bwu, rb, gb, br
#
# brwrr
# bggr
# gbbr
# rrbgbr
# ubwu
# bwurrg
# brgr
# bbrgwb'''

part1(INPUT)
part2(INPUT)
