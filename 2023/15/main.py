import lib.aoc

input_content = lib.aoc.get_current_input()
segments = input_content.split(',')

def hash_value(s: str):
    cur = 0
    for code in s.encode('ascii'):
        cur += code
        cur *= 17
        cur %= 256
    return cur

s = 0
s2 = 0

for segment in segments:
    s += hash_value(segment)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)