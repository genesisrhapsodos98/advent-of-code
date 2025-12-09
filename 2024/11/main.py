from collections import defaultdict

import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

stones = defaultdict(int)

for s in lines[0].split(" "):
    stones[int(s)] += 1


def blink(stone):
    if stone == 0:
        return [1]
    elif len(str(stone)) % 2 == 0:
        s = str(stone)
        l = s[:len(s) // 2]
        r = s[len(s) // 2:]
        return [int(l), int(r)]
    else:
        return [stone * 2024]


def fast_blink(stones):
    new_stones = defaultdict(int)
    for current_stone, stone_count in stones.items():
        for new_stone in blink(current_stone):
            new_stones[new_stone] += stone_count
    return new_stones


original_stones = stones.copy()
for i in range(25):
    stones = fast_blink(stones)

s = 0
for stone in stones:
    s += stones[stone]

stones = original_stones
for i in range(75):
    stones = fast_blink(stones)

s2 = 0
for stone in stones:
    s2 += stones[stone]

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)
