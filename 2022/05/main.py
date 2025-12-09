import parse
import lib.aoc

def parse_input(s):
    stacks, moves = s.split('\n\n')

    stack_lines = stacks.splitlines()

    stacks = [[] for _ in range(len(stack_lines.pop().split()))]

    for row in stack_lines[::-1]:
        for i, entry in enumerate(row[1::4]):
            if entry != ' ':
                stacks[i].append(entry)

    moves = parse.findall('move {:d} from {:d} to {:d}', moves)

    return stacks, moves

def solve(stacks, moves, move_fn):
    for n, source, target in moves:
        move_fn(stacks, n, source-1, target-1)

    return ''.join(s[-1] for s in stacks)

def part1(s):
    stacks, moves = parse_input(s)
    def move_blocks(stacks, n, source, target):
        for _ in range(n):
            stacks[target].append(stacks[source].pop(-1))
    answer = solve(stacks, moves, move_blocks)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    stacks, moves = parse_input(s)

    def move_blocks(stacks, n, source, target):
        moved = stacks[source][-n:]
        stacks[source] = stacks[source][:-n]
        stacks[target] += moved

    answer = solve(stacks, moves, move_blocks)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
