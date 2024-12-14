import lib.aoc

input_content = lib.aoc.get_current_input()
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
    m, m_rem = divmod(px * by - py * bx,  ax * by - ay * bx)
    if m_rem != 0 or m < 0:
        return 0

    n, n_rem = divmod(py - ay * m, by)
    if n_rem != 0 or n < 0:
        return 0

    return a_token_cost * m + b_token_cost * n

for i, prize in enumerate(prizes):
    ax, ay = a_increments[i]
    bx, by = b_increments[i]
    px, py = prize

    s += solve_machine(ax, ay, bx, by, px, py)
    s2 += solve_machine(ax, ay, bx, by, px + offset, py + offset)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)