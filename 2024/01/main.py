import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

pairs = [line.split('   ') for line in lines]
rotated = list(zip(*pairs[::-1]))

left = list(map(int, rotated[0]))
right = list(map(int, rotated[1]))


def part_1(left, right):
    s = 0
    while len(left) > 0:
        min_left = min(left)
        min_right = min(right)
        diff = abs(min_left - min_right)
        s += diff
        left.remove(min_left)
        right.remove(min_right)
    return s


def part_2(left, right):
    s = 0
    for num in left:
        appearance = right.count(num)
        s += num * appearance
    return s

r1 = part_1(left[:], right[:])
r2 = part_2(left[:], right[:])

lib.aoc.give_answer_current(1, r1)
lib.aoc.give_answer_current(2, r2)

