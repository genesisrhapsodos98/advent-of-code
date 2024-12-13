import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

operators = ['+', '*']
additional_operators = ['+', '*', '||']

equations = [line.split(': ') for line in lines]
lhs = [int(equation[0]) for equation in equations]
rhs = [equation[1].split(' ') for equation in equations]
rhs = [[int(num) for num in line] for line in rhs]

line_count = len(equations)

def try_operators(x, concat=False):
    if len(x) == 1:
        yield x[0]
    else:
        for sub in try_operators(x[1:], concat):
            yield x[0] + sub
            yield x[0] * sub

            if concat is True:
                yield int(str(sub) + str(x[0]))


s = 0
s2 = 0

for left, right in zip(lhs, rhs):
    for y in try_operators(right[::-1]):
        if y == left:
            s += left
            break
    for y in try_operators(right[::-1], True):
        if y == left:
            s2 += left
            break

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)