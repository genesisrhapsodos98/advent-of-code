import collections
import functools
import itertools
import math
import re
from collections import defaultdict

import lib.aoc
import lib.graph
import lib.grid

Part = collections.namedtuple('Part',
                              ('x', 'm', 'a', 's'))


def parse_input(s):
    s_workflows, s_ratings = s.split('\n\n')
    workflows = defaultdict(list)
    ratings = []
    for sw in s_workflows.splitlines():
        workflow = []
        label, rules = sw.split('{')
        for rule in rules[:-1].split(','):
            if ':' in rule:
                l, r = rule.split(':')
                workflow.append((l[0], l[1], int(l[2:]), r))
            else:
                workflow.append((None, None, None, rule))
        workflows[label] = workflow

    for sr in s_ratings.splitlines():
        rating = dict()
        for part in sr[1:-1].split(','):
            l, r = part.split('=')
            rating[l] = int(r)
        ratings.append(rating)

    return workflows, ratings


def solve_rule(workflow, rating):
    for rule in workflow:
        target, op, num, to = rule

        if target is None:
            return to

        t_num = rating[target]
        condition = (t_num > num) if op == '>' else (t_num < num)
        if condition:
            return to


def evaluate(rating: dict):
    return sum(rating.values())


def part1(s):
    workflows, ratings = parse_input(s)
    answer = 0

    for rating in ratings:
        cur = 'in'
        while cur not in 'AR':
            cur_workflow = workflows[cur]
            cur = solve_rule(cur_workflow, rating)
        if cur == 'A':
            answer += evaluate(rating)

    lib.aoc.give_answer_current(1, answer)


def filter_rule(rule, part: Part):
    target, op, num, to = rule
    if target is None:
        return part, None

    filter_good = (lambda v: v[:v.index(num)]) if op == '<' else (lambda v: v[v.index(num) + 1:])
    filter_bad = (lambda v: v[v.index(num):]) if op == '<' else (lambda v: v[:v.index(num) + 1])
    test = (lambda n: n < num) if op == '<' else (lambda n: n > num)

    vals = getattr(part, target)
    if num in vals:
        good = part._replace(**{target: filter_good(vals)})
        bad = part._replace(**{target: filter_bad(vals)})
        return good, bad
    elif len(vals) > 0:
        if test(vals[0]):
            return part, part._replace(**{target: range(0)})
        else:
            return part._replace(**{target: range(0)}), part
    else:
        return part, part


def walk_rule(workflows, label, part: Part):
    if label == 'A':
        return len(part.x) * len(part.m) * len(part.a) * len(part.s)
    if label == 'R':
        return 0

    count = 0

    for rule in workflows[label]:
        target, op, num, to = rule
        good, part = filter_rule(rule, part)
        if good is not None:
            count += walk_rule(workflows, to, good)
        if part is None:
            break

    return count


def part2(s):
    workflows, _ = parse_input(s)

    start_label = 'in'

    answer = walk_rule(workflows, start_label, Part(
        range(1, 4001),
        range(1, 4001),
        range(1, 4001),
        range(1, 4001)))
    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
