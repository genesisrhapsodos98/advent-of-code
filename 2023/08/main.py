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


lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)