import lib.aoc

def parse_input(s):
    pairs = s.split(',')
    ranges = [tuple(map(int, pair.split('-'))) for pair in pairs]
    return ranges

def repeated_twice_pattern(s):
    n = len(s)
    if n % 2 != 0:
        return None

    half = n // 2
    unit = s[:half]

    if unit * 2 == s:
        return unit

    return None

def smallest_repeated_pattern(s):
    n = len(s)
    for i in range(1, n // 2 + 1):
        if n % i == 0:
            unit = s[:i]
            if unit * (n // i) == s:
                return unit
    return None

def part1(s):
    ranges = parse_input(s)
    answer = 0
    for (start, end) in ranges:
        for n in range(start, end + 1):
            p = repeated_twice_pattern(str(n))
            if p is not None:
                answer += n
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    ranges = parse_input(s)
    answer = 0
    for (start, end) in ranges:
        for n in range(start, end + 1):
            p = smallest_repeated_pattern(str(n))
            if p is not None:
                answer += n
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
