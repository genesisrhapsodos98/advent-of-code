import functools

import lib.aoc
import lib.graph
import lib.grid

wires = dict()
simulations = dict()


def parse_input(s):
    groups = s.split('\n\n')
    for line in groups[0].splitlines():
        a, b = line.split(':')
        wires[a] = b.strip() == '1'
    for line in groups[1].splitlines():
        src, dst = line.split(' -> ')
        a, op, b = src.split()
        simulations[dst] = (a, op, b)


def evaluate(a, op, b):
    match op:
        case 'AND':
            return a & b
        case 'OR':
            return a | b
        case _:
            return a ^ b


@functools.cache
def deep_evaluate(simulation):
    a, op, b = simulation
    if a in wires and b in wires:
        return evaluate(wires[a], op, wires[b])
    new_a = a
    new_b = b
    if new_a not in wires:
        new_a = deep_evaluate(simulations[a])
    if new_b not in wires:
        new_b = deep_evaluate(simulations[b])
    return evaluate(new_a, op, new_b)


def part1(s):
    parse_input(s)
    targets = sorted([s for s in simulations if s.startswith('z')])[::-1]
    binary_str = ''
    for t in targets:
        simulation = simulations[t]
        result = deep_evaluate(simulation)
        binary_str += '1' if result else '0'

    answer = int(binary_str, 2)
    lib.aoc.give_answer_current(1, answer)


@functools.cache
def inspect(simulation, depth=0):
    if simulation in wires or depth >= 5:
        return simulation
    a, op, b = simulations[simulation]
    simulation_1 = inspect(a, depth + 1)
    simulation_2 = inspect(b, depth + 1)

    if op == 'AND':
        return f'{simulation}{{({simulation_1}) & ({simulation_2})}}'
    if op == 'OR':
        return f'{simulation}{{({simulation_1}) | ({simulation_2})}}'
    if op == 'XOR':
        return f'{simulation}{{({simulation_1}) ^ ({simulation_2})}}'


def swap(a, b):
    tmp = simulations[a]
    simulations[a] = simulations[b]
    simulations[b] = tmp


def part2(s):
    # Ripple adder circuit
    # For every bit position n:
    # (1) = xn ^ yn
    # (2) = xn & yn
    # carry{n} = (2) | ((1) ^ carry{n-1})
    # z{n} = (1) ^ carry{n-1}
    # Use the inspect function to check which z does not conform to these rules
    pairs = [('z12', 'kwb'), ('z16', 'qkf'), ('z24', 'tgr'),
             ('jqn', 'cph')]  # Start with empty array, then add any pair you find
    for a, b in pairs:
        swap(a, b)
    deep_evaluate.cache_clear()

    x_wires = sorted([w for w in wires if w.startswith('x')])[::-1]
    y_wires = sorted([w for w in wires if w.startswith('y')])[::-1]
    z_wires = sorted([s for s in simulations if s.startswith('z')])[::-1]

    x_str = ''.join(['1' if wires[x] else '0' for x in x_wires])
    y_str = ''.join(['1' if wires[y] else '0' for y in y_wires])
    z_str = ''
    for z in z_wires:
        simulation = simulations[z]
        result = deep_evaluate(simulation)
        z_str += '1' if result else '0'

    true_z_str = bin(int(x_str, 2) + int(y_str, 2))[2:]
    # print(f'{true_z_str} -> {int(x_str, 2) + int(y_str, 2)}')
    # print(z_str)

    for i in range(len(true_z_str)):
        print(inspect(f"z{i:02}"))

    result = set()
    for a, b in pairs:
        result.add(a)
        result.add(b)
    answer = ','.join(sorted(result))
    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
