import functools

import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

rows = []

for line in lines:
    seg_l, seg_r = line.split(' ')
    conditions = list(map(int, seg_r.split(',')))
    rows.append((seg_l, conditions))

@functools.cache
def count_matches(pattern, condition):
    a = condition[0]
    rest = condition[1:]
    after = sum(rest) + len(rest)

    count = 0

    for before in range(len(pattern) - after - a + 1):
        if all(c in '#?' for c in pattern[before:before + a]):
            if len(rest) == 0:
                if all(c in '.?' for c in pattern[before + a:]):
                    count += 1
            elif pattern[before + a] in '.?':
                count += count_matches(pattern[before + a + 1:], rest)

        if pattern[before] not in '.?':
            break
    return count


def solve_row(row, copies=1):
    answer = 0
    pattern, condition = row

    pattern = '?'.join((pattern,) * copies)
    condition = tuple(condition) * copies

    answer += count_matches(pattern, tuple(condition))
    return answer


s = 0
s2 = 0

for row in rows:
    s += solve_row(row)
    s2 += solve_row(row, 5)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)
