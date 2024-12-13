import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

s = 0
s2 = 0

for line in lines:
    digits = [c for c in line if c.isdigit()]
    first = int(digits[0])
    last = int(digits[-1])
    s += 10 * first + last

lib.aoc.give_answer_current(1, s)
# lib.aoc.give_answer_current(2, s2)