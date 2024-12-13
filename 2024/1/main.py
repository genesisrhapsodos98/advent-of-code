input_file = open(".\\input.txt", "r")
input_content = input_file.read()
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


print(part_1(left[:], right[:]))
print(part_2(left[:], right[:]))
