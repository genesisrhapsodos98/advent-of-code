import math
from collections import defaultdict

import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

instructions = lines[0]

start = 'AAA'
end = 'ZZZ'

nodes = defaultdict(list)
for line in lines[2:]:
    node_data = line.split('=')
    key = node_data[0].strip()
    [l, r] = node_data[1].strip()[1:9].split(', ')
    nodes[key] = [l, r]

s = 0
s2 = 0

current = start
while current != end:
    instruction = instructions[s % len(instructions)]
    [left, right] = nodes[current]
    current = left if instruction == 'L' else right
    s += 1

start_keys = [key for key in nodes.keys() if key[-1] == 'A']

rs = []
for key in start_keys:
    r = 0
    while key[-1] != 'Z':
        instruction = instructions[r % len(instructions)]
        [left, right] = nodes[key]
        key = left if instruction == 'L' else right
        r += 1
    rs.append(r)
s2 = math.lcm(*rs)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)