import lib.aoc

def parse_input(s):
    lines = s.splitlines()
    instructions = []
    for line in lines:
        direction = line[0]
        amount = int(line[1:])
        instructions.append((direction, amount))
    return instructions

def part1(s):
    instructions = parse_input(s)
    current = 50
    answer = 0
    for (d, a) in instructions:
        delta = a if d == 'R' else -a
        previous = current
        end = previous + delta
        current = end % 100
        if current == 0:
            answer += 1
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    instructions = parse_input(s)
    current = 50
    answer = 0
    for (d, a) in instructions:
        delta = a if d == 'R' else -a
        previous = current
        end = previous + delta

        if delta > 0:
            times = (end // 100) - (previous // 100)
        else:
            times = ((previous - 1) // 100) - ((end - 1) // 100)

        answer += times
        current = end % 100

    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
