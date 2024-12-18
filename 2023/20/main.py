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
    pulses = collections.Counter()
    queue = [(modules, conjunction_inputs, target, signal)]
    while len(queue) > 0:
        modules, conjunction_inputs, target, signal = queue.pop(0)
        pulses[signal] += 1
        if target not in modules:
            continue
        m_type, dst, state = modules[target]
        if m_type is None:
            modules[target] = m_type, dst, signal
            for m in dst:
                queue.append((modules, conjunction_inputs, m, signal))
        elif m_type == '%':
            if signal is True:
                continue
            else:
                state = not state
                modules[target] = m_type, dst, state
                for m in dst:
                    queue.append((modules, conjunction_inputs, m, state))
        else:
            conjunctions = [v for k, v in modules.items() if k in conjunction_inputs[target]]
            all_inputs_high = all([n_state == True for _, _, n_state in conjunctions])
            if all_inputs_high:
                modules[target] = m_type, dst, False
                for m in dst:
                    queue.append((modules, conjunction_inputs, m, False))
            else:
                modules[target] = m_type, dst, True
                for m in dst:
                    queue.append((modules, conjunction_inputs, m, True))
    return pulses

def part1(s):
    modules, conjunction_inputs = parse_input(s)

    pulses = collections.Counter()
    for _ in range(1000):
        n_pulses = send_pulse(modules, conjunction_inputs, 'broadcaster', False)
        pulses += n_pulses

    answer = pulses[True] * pulses[False]

    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
##    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
