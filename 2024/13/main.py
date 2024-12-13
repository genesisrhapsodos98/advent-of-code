input_file = open('.\\input.txt', 'r')
input_content = input_file.read()
groups = input_content.split('\n\n')

a_increments = []
b_increments = []
prizes = []

a_token_cost = 3
b_token_cost = 1
offset = 10000000000000

for group in groups:
    components = [line.split(':') for line in group.split('\n')]

    a_component = components[0][1].split(',')
    ax, ay = (int(a_component[0].split('+')[1]), int(a_component[1].split('+')[1]))
    a_increments.append((ax, ay))

    b_component = components[1][1].split(',')
    bx, by = (int(b_component[0].split('+')[1]), int(b_component[1].split('+')[1]))
    b_increments.append((bx, by))

    p_component = components[2][1].split(',')
    px, py = (int(p_component[0].split('=')[1]), int(p_component[1].split('=')[1]))
    prizes.append((px, py))

s = 0
s2 = 0

def solve_machine(ax, ay, bx, by, px, py):
    m = (px * by - py * bx) // (ax * by - ay * bx)
    if m * (ax * by - ay * bx) != (px * by - py * bx):
        return 0

    n = (py - ay * m) // by
    if n * by != (py - ay * m):
        return 0

    return a_token_cost * m + b_token_cost * n

for i, prize in enumerate(prizes):
    ax, ay = a_increments[i]
    bx, by = b_increments[i]
    px, py = prize

    s += solve_machine(ax, ay, bx, by, px, py)
    s2 += solve_machine(ax, ay, bx, by, px + offset, py + offset)

print(s)
print(s2)