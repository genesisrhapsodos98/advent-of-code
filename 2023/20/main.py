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
    lines = s.splitlines()
    modules = dict()
    conjunction_inputs = defaultdict(list)
    conjunctions = []
    for line in lines:
        src, r = line.split(' -> ')
        dst = r.split(', ')
        if src == 'broadcaster':
            modules[src] = (None, dst, False)
            continue
        m_type, m_name = src[0], src[1:]
        modules[m_name] = (m_type, dst, False)
        if m_type == '&':
            conjunctions.append(m_name)

    for k, m in modules.items():
        m_type, dst, state = m
        for d in dst:
            if d in conjunctions:
                conjunction_inputs[d].append(k)
    return modules, conjunction_inputs

def send_pulse(modules, conjunction_inputs, target, signal):
    low, high = 0, 0
    m_type, dst, state = modules[target]
    if m_type is None:
        for m in dst:
            l, h = send_pulse(modules, m, signal)
            low += l
            high += h
    elif m_type == '%':
        if signal is True:
            return low, high

    return low, high

def part1(s):
    modules, conjunction_inputs = parse_input(s)
    answer = 0

    low, high = 0, 0
    for _ in range(1000):
        l, h = send_pulse(modules, conjunction_inputs, 'broadcaster', False)
        low += l
        high += h

    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
##    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
