import collections
import functools
import itertools
import math
import re
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

output = []

def adv(operand, a, b, c, instr):
    num, denom = a, 2 ** resolve_combo(operand, a, b, c)
    result = num // denom
    return result, b, c, instr + 2

def bxl(operand, a, b, c, instr):
    l, r = b, operand
    result = l ^ r
    return a, result, c, instr + 2

def bst(operand, a, b, c, instr):
    num = resolve_combo(operand, a, b, c)
    result = num % 8
    return a, result ,c, instr + 2

def jnz(operand, a, b, c, instr):
    if a == 0:
        return a, b, c, instr + 2
    instr = operand
    return a, b, c, instr

def bxc(operand, a, b, c, instr):
    result = b ^ c
    return a, result, c, instr + 2

def out(operand, a, b, c, instr):
    combo = resolve_combo(operand, a, b, c)
    result = combo % 8
    output.append(str(result))
    return a, b, c, instr + 2

def bdv(operand, a, b, c, instr):
    num, denom = a, 2 ** resolve_combo(operand, a, b, c)
    result = num // denom
    return a, result, c, instr + 2

def cdv(operand, a, b, c, instr):
    num, denom = a, 2 ** resolve_combo(operand, a, b, c)
    result = num // denom
    return a, b, result, instr + 2

instructions = [adv, bxl, bst, jnz, bxc, out, bdv, cdv]

def part1(s):
    top, bottom = s.split('\n\n')
    a, b, c = [int(line.split(': ')[1])for line in top.splitlines()]
    program = list(map(int, bottom.split(':')[1].split(',')))

    cur = 0
    while 0 <= cur < len(program):
        op_code = program[cur]
        operand = program[cur + 1]
        instruction = instructions[op_code]
        a, b, c, cur = instruction(operand, a, b, c, cur)

    answer = ','.join(output)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
##    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
