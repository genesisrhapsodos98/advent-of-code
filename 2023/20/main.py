import collections
import math
from collections import defaultdict

import lib.aoc
import lib.graph
import lib.grid


def parse_input(s):
    lines = s.splitlines()
    modules = dict()
    conjunction_inputs = defaultdict(list)
    for line in lines:
        src, r = line.split(' -> ')
        dst = r.split(', ')
        if src == 'broadcaster':
            modules[src] = (None, dst, False)
            continue
        m_type, m_name = src[0], src[1:]
        modules[m_name] = (m_type, dst, False)

    modules['rx'] = (None, [], None)

    for k, m in modules.items():
        m_type, dst, state = m
        for d in dst:
            conjunction_inputs[d].append(k)

    return modules, conjunction_inputs


def send_pulse(modules, conjunction_inputs, target, signal, tracked_modules=None):
    pulses = collections.Counter()
    queue = [(modules, conjunction_inputs, target, signal)]
    tracked_signals = []
    while len(queue) > 0:
        modules, conjunction_inputs, target, signal = queue.pop(0)
        pulses[signal] += 1

        if tracked_modules is not None:
            if target in tracked_modules and not signal:
                tracked_signals.append(target)
        if target not in modules or target == 'rx':
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
    return pulses, tracked_signals


def part1(s):
    modules, conjunction_inputs = parse_input(s)

    pulses = collections.Counter()
    for _ in range(1000):
        n_pulses, _ = send_pulse(modules, conjunction_inputs, 'broadcaster', False)
        pulses += n_pulses

    answer = pulses[True] * pulses[False]

    lib.aoc.give_answer_current(1, answer)


def num_cycles_until_low_output(modules, conjunction_inputs):
    # Assumptions:
    # 1) There is a single output node
    # 2) That output node is fed by a single conjunction module
    # 3) That conjunction module is fed by n conjunction modules
    # 4) The broadcast node outputs to n modules
    # 5) Each of those outputs from broadcast links to a distinct
    # subtree which reaches one of the final conjuction modules
    # 6) Each subtree regularly outputs a low pulse after a set number of
    # button presses

    output = 'rx'

    output_feeds = conjunction_inputs[output]
    assert (len(output_feeds) == 1)

    # Must be fed a high signal to output a low signal
    output_feed = list(output_feeds)[0]
    assert (modules[output_feed][0] == '&')

    # These must be fed a low signal to output a high signal
    subtree_leaves = conjunction_inputs[output_feed]
    assert (all(modules[leaf][0] == '&'
                for leaf in subtree_leaves))

    subtree_cycles = {}
    cycle = 0

    while len(subtree_cycles) < len(subtree_leaves):
        cycle += 1

        _, tracked_signals = send_pulse(modules, conjunction_inputs, 'broadcaster', False, subtree_leaves)

        for leaf in tracked_signals:
            if leaf in subtree_cycles:
                continue
            subtree_cycles[leaf] = cycle

    return math.lcm(*subtree_cycles.values())


def part2(s):
    modules, conjunction_inputs = parse_input(s)

    answer = num_cycles_until_low_output(modules, conjunction_inputs)
    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
