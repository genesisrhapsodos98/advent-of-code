import math

import lib.aoc

input_content = lib.aoc.get_current_input()
groups = input_content.split('\n\n')

seeds = []
maps = []

def solve(seed_ranges):
    for m in maps:
        new_ranges = []
        for start, r_len in seed_ranges:
            while r_len != 0:
                found_match = False
                best_dist = r_len

                for dst, src, length in m:
                    if src <= start < src + length:
                        offset = start - src
                        rem_length = min(length - offset, r_len)
                        new_ranges.append((dst + offset, rem_length))
                        start += rem_length
                        r_len -= rem_length
                        found_match = True
                        break
                    elif start < src:
                        best_dist = min(src - start, best_dist)

                if not found_match:
                    handling_len = min(best_dist, r_len)
                    new_ranges.append((start, handling_len))
                    start += handling_len
                    r_len -= handling_len

        seed_ranges = new_ranges
    return min(start for start, length in seed_ranges)



for idx, group in enumerate(groups):
    if idx == 0:
        data = group.split(':')[1]
        seeds = [int(seed.strip()) for seed in data.split(' ') if seed != '']
    else:
        m = [tuple(map(int, l.split())) for l in group.splitlines()[1:]]
        maps.append(m)

seed_ranges = [(seed, 1) for seed in seeds]

s = solve(seed_ranges)

seed_ranges = list(zip(seeds[::2], seeds[1::2]))

s2 = solve(seed_ranges)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)