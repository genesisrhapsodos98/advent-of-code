import lib.aoc
import lib.graph
import lib.grid


def resolve_combo(operand, a, b, c):
    match operand:
        case operand if operand <= 3:
            return operand
        case 4:
            return a
        case 5:
            return b
        case 6:
            return c
        case _:
            assert False


def adv(operand, a, b, c, instr, output):
    num, denom = a, 2 ** resolve_combo(operand, a, b, c)
    result = num // denom
    return result, b, c, instr + 2


def bxl(operand, a, b, c, instr, output):
    l, r = b, operand
    result = l ^ r
    return a, result, c, instr + 2


def bst(operand, a, b, c, instr, output):
    num = resolve_combo(operand, a, b, c)
    result = num % 8
    return a, result, c, instr + 2


def jnz(operand, a, b, c, instr, output):
    if a == 0:
        return a, b, c, instr + 2
    instr = operand
    return a, b, c, instr


def bxc(operand, a, b, c, instr, output):
    result = b ^ c
    return a, result, c, instr + 2


def out(operand, a, b, c, instr, output):
    combo = resolve_combo(operand, a, b, c)
    result = combo % 8
    output.append(str(result))
    return a, b, c, instr + 2


def bdv(operand, a, b, c, instr, output):
    num, denom = a, 2 ** resolve_combo(operand, a, b, c)
    result = num // denom
    return a, result, c, instr + 2


def cdv(operand, a, b, c, instr, output):
    num, denom = a, 2 ** resolve_combo(operand, a, b, c)
    result = num // denom
    return a, b, result, instr + 2


instructions = [adv, bxl, bst, jnz, bxc, out, bdv, cdv]


def part1(s):
    top, bottom = s.split('\n\n')
    a, b, c = [int(line.split(': ')[1]) for line in top.splitlines()]
    program = list(map(int, bottom.split(':')[1].split(',')))

    answer = run_program(a, b, c, program)
    lib.aoc.give_answer_current(1, answer)


def run_program(a, b, c, program):
    output = []
    cur = 0
    visited = set()
    while 0 <= cur < len(program):
        state = (a, b, c, cur)
        if state in visited:
            break
        visited.add(state)
        op_code = program[cur]
        operand = program[cur + 1]
        instruction = instructions[op_code]
        a, b, c, cur = instruction(operand, a, b, c, cur, output)

    return ','.join(output)


def part2(s):
    top, bottom = s.split('\n\n')
    oa, ob, oc = [int(line.split(': ')[1]) for line in top.splitlines()]
    program = list(map(int, bottom.split(':')[1].split(',')))

    # Starting 'a' determines the length of the result
    # In order to have a result of length L, 'a' must be from 8 ** (L - 1) to 8 ** L - 1
    # The nth digit from the right of the result changes every 8 ** (L - n) - 1
    # So in order to find the first occurrence of <program> in result,
    # we need to start 'a' from 8 ** (L - 1)
    # then we increase 'a' by 8 ** (L - n) where n is the number of matching digits from right to left,
    # stopping as soon as we see a complete match between answer and program
    start = 8 ** (len(program) - 1)
    na = start

    flipped = bottom.split(': ')[1][::-1]

    answer = ''
    while flipped != answer:
        a, b, c = na, ob, oc

        matching = 0
        answer = run_program(a, b, c, program)[::-1]
        for i in range(len(flipped))[::2]:
            l, r = flipped[i], answer[i]
            if l != r:
                break
            matching += 1
        step = 8 ** (len(program) - matching - 1)
        if step < 1:
            break
        na += step
    lib.aoc.give_answer_current(2, na)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
