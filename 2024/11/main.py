from collections import defaultdict

input_file = open('.\\input.txt', 'r')
input_content = input_file.read()
lines = input_content.split('\n')

stones = defaultdict(int)

for s in lines[0].split(" "):
    stones[int(s)] += 1


def step(stone):
    if stone == 0:
        return [1]
    elif len(str(stone)) % 2 == 0:
        s = str(stone)
        l = s[:len(s) // 2]
        r = s[len(s) // 2:]
        return [int(l), int(r)]
    else:
        return [stone * 2024]


def fast_step(stones):
    new_stones = defaultdict(int)
    for current_stone, stone_count in stones.items():
        for new_stone in step(current_stone):
            new_stones[new_stone] += stone_count
    return new_stones


original_stones = stones.copy()
for i in range(25):
    stones = fast_step(stones)

s = 0
for stone in stones:
    s += stones[stone]
print(s)

stones = original_stones
for i in range(75):
    stones = fast_step(stones)

s2 = 0
for stone in stones:
    s2 += stones[stone]
print(s2)
