import collections
from collections import defaultdict

import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
grid = FixedGrid.parse(input_content)

antennas = defaultdict(list)
antinodes = collections.Counter()
updated_antinodes = collections.Counter()

for coords, v in grid.items():
    if v == '.':
        continue
    antennas[v].append(coords)

for frequency in antennas:
    frequency_antennas = antennas[frequency]
    for i in range(len(frequency_antennas) - 1):
        for j in range(i + 1, len(frequency_antennas)):
            ax, ay = frequency_antennas[i]
            bx, by = frequency_antennas[j]

            found_antinodes = collections.Counter()
            found_updated_antinodes = collections.Counter()
            found_updated_antinodes[(ax, ay)] += 1
            found_updated_antinodes[(bx, by)] += 1

            dx, dy = (ax - bx, ay - by)

            multiplier = 1
            in_bound = True
            while in_bound:
                found_antinode_1 = (ax + dx * multiplier, ay + dy * multiplier)
                found_antinode_2 = (bx - dx * multiplier, by - dy * multiplier)

                if found_antinode_1 not in grid and found_antinode_2 not in grid:
                    in_bound = False
                else:
                    if found_antinode_1 in grid:
                        if multiplier == 1:
                            found_antinodes[found_antinode_1] += 1
                        found_updated_antinodes[found_antinode_1] += 1

                    if found_antinode_2 in grid:
                        if multiplier == 1:
                            found_antinodes[found_antinode_2] += 1
                        found_updated_antinodes[found_antinode_2] += 1

                    multiplier += 1

            for a in found_antinodes.keys():
                antinodes[a] += found_antinodes[a]

            for a in found_updated_antinodes.keys():
                updated_antinodes[a] += found_updated_antinodes[a]

s = len(antinodes)
s2 = len(updated_antinodes)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)