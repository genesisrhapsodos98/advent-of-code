import collections
import functools
import itertools
import math
import re
from collections import defaultdict

import lib.aoc
import lib.graph
import lib.grid

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
        condition =  (t_num > num) if op == '>' else (t_num < num)
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

    print(f'The answer to part one is {answer}')
    if input('Submit answer? ').lower() in ('y', 'yes', '1'):
        assert(lib.aoc.give_answer_current(1, answer))

def part2(s):
    pass
##    print(f'The answer to part two is {answer}')
##    if input('Submit answer? ').lower() in ('y', 'yes', '1'):
##        assert(lib.aoc.give_answer_current(2, answer))

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
