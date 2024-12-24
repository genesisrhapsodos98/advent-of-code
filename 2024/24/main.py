import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid
from lib.graphics import *


def parse_input(s):
    groups = s.split('\n\n')
    wires = dict()
    simulations = dict()
    for line in groups[0].splitlines():
        a, b = line.split(':')
        wires[a] = b.strip() == '1'
    for line in groups[1].splitlines():
        src, dst = line.split(' -> ')
        a, op, b = src.split()
        simulations[dst] = (a, op, b)
    return wires, simulations

def evaluate(a, op, b):
    match op:
        case 'AND':
            return a & b
        case 'OR':
            return a | b
        case _:
            return a ^ b

def traverse(simulation, wires, simulations):
    a, op, b = simulation
    if a in wires and b in wires:
        return evaluate(wires[a], op, wires[b])
    new_a = a
    new_b = b
    if new_a not in wires:
        new_a = traverse(simulations[a], wires, simulations)
    if new_b not in wires:
        new_b= traverse(simulations[b], wires, simulations)
    return evaluate(new_a, op, new_b)



def part1(s):
    wires, simulations = parse_input(s)
    targets = sorted([s for s in simulations if s.startswith('z')])[::-1]
    binary_str = ''
    for t in targets:
        simulation = simulations[t]
        result = traverse(simulation, wires, simulations)
        binary_str += '1' if result else '0'

    answer = int(binary_str, 2)
    lib.aoc.give_answer_current(1, answer)


def part2(s):
    pass
    _ = parse_input(s)
    answer = 0
    # lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
# INPUT = '''x00: 1
# x01: 1
# x02: 1
# y00: 0
# y01: 1
# y02: 0
#
# x00 AND y00 -> z00
# x01 XOR y01 -> z01
# x02 OR y02 -> z02'''
part1(INPUT)
part2(INPUT)
