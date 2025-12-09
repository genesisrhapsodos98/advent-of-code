import math

import lib.aoc
import lib.graph
import lib.grid

visited = dict()


def cheapest_arrow_pad(cur_row, cur_col, dest_row, dest_col, n_robots):
    answer = math.inf

    state = (cur_row, cur_col, dest_row, dest_col, n_robots)

    if state in visited:
        return visited[(cur_row, cur_col, dest_row, dest_col, n_robots)]

    queue = [(cur_row, cur_col, '')]
    while queue:
        row, col, presses = queue.pop(0)
        if row == dest_row and col == dest_col:
            rec = cheapest_robot(presses + 'A', n_robots - 1)
            answer = min(answer, rec)
            continue

        if row == 0 and col == 0:
            continue

        else:
            if row < dest_row:
                queue.append((row + 1, col, presses + 'v'))
            elif row > dest_row:
                queue.append((row - 1, col, presses + '^'))
            if col < dest_col:
                queue.append((row, col + 1, presses + '>'))
            elif col > dest_col:
                queue.append((row, col - 1, presses + '<'))

    visited[state] = answer
    return answer


def cheapest_robot(presses, n_robots):
    if n_robots == 1:
        return len(presses)

    result = 0
    pad_config = 'X^A<v>'

    cur_row = 0
    cur_col = 2

    for i in range(len(presses)):
        for next_row in range(0, 2):
            for next_col in range(0, 3):
                if pad_config[next_row * 3 + next_col] == presses[i]:
                    result += cheapest_arrow_pad(cur_row, cur_col, next_row, next_col, n_robots)
                    cur_row = next_row
                    cur_col = next_col

    return result


def cheapest(cur_row, cur_col, dest_row, dest_col, n_robots):
    answer = math.inf
    queue = [(cur_row, cur_col, '')]

    while queue:
        row, col, presses = queue.pop(0)
        if row == dest_row and col == dest_col:
            rec = cheapest_robot(presses + 'A', n_robots)
            answer = min(answer, rec)
            continue

        if row == 3 and col == 0:
            continue

        else:
            if row < dest_row:
                queue.append((row + 1, col, presses + 'v'))
            elif row > dest_row:
                queue.append((row - 1, col, presses + '^'))
            if col < dest_col:
                queue.append((row, col + 1, presses + '>'))
            elif col > dest_col:
                queue.append((row, col - 1, presses + '<'))

    return answer


def solve(codes, n_robots):
    total = 0
    pad_config = '789456123X0A'

    cur_row = 3
    cur_col = 2

    for code in codes:
        result = 0
        for i in range(len(code)):
            for next_row in range(0, 4):
                for next_col in range(0, 3):
                    if pad_config[next_row * 3 + next_col] == code[i]:
                        result += cheapest(cur_row, cur_col, next_row, next_col, n_robots)
                        cur_row = next_row
                        cur_col = next_col

        total += result * int(code[:-1])

    return total


def parse_input(s):
    codes = s.splitlines()
    return codes


def part1(s):
    codes = parse_input(s)
    answer = solve(codes, 3)
    lib.aoc.give_answer_current(1, answer)


def part2(s):
    codes = parse_input(s)
    answer = solve(codes, 26)
    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
