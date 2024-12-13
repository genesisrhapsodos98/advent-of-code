import re
import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

valid_commands = []

for line in lines:
    matches = [r for r in re.findall("(?:mul\((\d+),(\d+)\))|(do\(\))|(don't\(\))", line)]
    for match in matches:
        valid_commands.append(match)

do_indexes = [i for i, e in enumerate(valid_commands) if e[2] == "do()"]
dont_indexes = [i for i, e in enumerate(valid_commands) if e[3] == "don't()"]

s = 0
for command in [command for command in valid_commands if command[0] != '' and command[1] != '']:
    s += int(command[0]) * int(command[1])

current_index = 0
for i in dont_indexes:
    if i < current_index:
        continue

    next_do_index = min([di for di in do_indexes if di > i])
    for ri in range(i, next_do_index):
        valid_commands[ri] = ('', '', '', '')
    current_index = next_do_index

s2 = 0
for command in [command for command in valid_commands if command[0] != '' and command[1] != '']:
    s2 += int(command[0]) * int(command[1])

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)