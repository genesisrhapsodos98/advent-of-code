import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

red = 12
green = 13
blue = 14

def parse_set(set):
    parts = set.split(',')
    r, g, b = 0, 0, 0
    for part in parts:
        v = int(''.join(filter(str.isdigit, part)))
        if 'red' in part:
            r += v
        if 'green' in part:
            g += v
        if 'blue' in part:
            b += v
    return r, g, b

s = 0
s2 = 0

for idx, line in enumerate(lines, 1):
    game = line.split(':')[1]
    sets = [x.strip() for x in game.split(';')]
    possible = True
    max_r, max_g, max_b = 0, 0, 0
    for x in sets:
        r, g, b = parse_set(x)

        max_r, max_g, max_b = max(max_r, r), max(max_g, g), max(max_b, b)

        if r > red or g > green or b > blue:
            possible = False
    if possible:
        s += idx
    s2 += max_r * max_g * max_b

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)