input_file = open('.\\input.txt')
input_content = input_file.read()
lines = input_content.split('\n')

operators = ['+', '*']
additional_operators = ['+', '*', '||']

equations = [line.split(': ') for line in lines]
lhs = [int(equation[0]) for equation in equations]
rhs = [equation[1].split(' ') for equation in equations]
rhs = [[int(num) for num in line] for line in rhs]

def solve_backtrack(solution, rhs, next_operators):
    if not ' ' in rhs and evaluate(rhs) == solution:
        return True

    for i in range(len(rhs)):
        if ' ' in rhs:
            idx = rhs.index(' ')
            results = []
            for operator in next_operators:
                new_rhs = rhs[:]
                new_rhs[idx] = operator
                results.append(solve_backtrack(solution, new_rhs, next_operators))
            return True in results

    return False

def evaluate(rhs):
    if ' ' in rhs:
        return 0
    result = rhs[0]
    next_operator = rhs[1]
    for elem in rhs[1:]:
        match elem:
            case '+':
                next_operator = '+'
            case '*':
                next_operator = '*'
            case '||':
                next_operator = '||'
            case _:
                if next_operator == '+':
                    result += elem
                elif next_operator == '*':
                    result *= elem
                else:
                    result = int(str(result) + str(elem))

    return result

line_count = len(equations)

# s = 0
# s2 = 0
#
# for i in range(line_count):
#     for j in range(0, len(rhs[i])):
#         rhs[i].insert(j * 2, " ")
#     rhs[i] = rhs[i][1:]
#     if solve_backtrack(lhs[i], rhs[i], operators):
#         s += lhs[i]
#     if solve_backtrack(lhs[i], rhs[i], additional_operators):
#         s2 += lhs[i]
#
# print(s)
# print(s2)

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

print(s)
print(s2)