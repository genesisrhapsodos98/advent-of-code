import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

map_height = len(lines)
map_width = len(lines[0])

antennas = {}
antinodes = {}
updated_antinodes = {}

def valid_coordinates(x, y, width, height):
    return 0 <= x < width and 0 <= y < height

for i in range(map_height):
    for j in range(map_width):
        if lines[i][j] == '.':
            continue
        if lines[i][j] in antennas:
            antennas[lines[i][j]].append((j, i))
        else:
            antennas[lines[i][j]] = [(j, i)]

for frequency in antennas:
    frequency_antennas = antennas[frequency]
    for i in range(len(frequency_antennas) - 1):
        for j in range(i + 1, len(frequency_antennas)):
            first_antenna = frequency_antennas[i]
            second_antenna = frequency_antennas[j]

            found_antinodes = {}
            found_updated_antinodes = {first_antenna: 1, second_antenna: 1}

            diff = (first_antenna[0] - second_antenna[0], first_antenna[1] - second_antenna[1])

            multiplier = 1
            in_bound = True
            while in_bound:
                found_antinode = (first_antenna[0] + diff[0] * multiplier, first_antenna[1] + diff[1] * multiplier)
                if valid_coordinates(found_antinode[0], found_antinode[1], map_width, map_height):
                    if multiplier == 1:
                        if (found_antinode[0], found_antinode[1]) in found_antinodes:
                            found_antinodes[(found_antinode[0], found_antinode[1])] += 1
                        else:
                            found_antinodes[(found_antinode[0], found_antinode[1])] = 1
                    if (found_antinode[0], found_antinode[1]) in found_updated_antinodes:
                        found_updated_antinodes[(found_antinode[0], found_antinode[1])] += 1
                    else:
                        found_updated_antinodes[(found_antinode[0], found_antinode[1])] = 1
                    multiplier += 1
                else:
                    in_bound = False



            multiplier = 1
            in_bound = True
            while in_bound:
                found_antinode = (second_antenna[0] - diff[0] * multiplier, second_antenna[1] - diff[1] * multiplier)
                if valid_coordinates(found_antinode[0], found_antinode[1], map_width, map_height):
                    if multiplier == 1:
                        if (found_antinode[0], found_antinode[1]) in found_antinodes:
                            found_antinodes[(found_antinode[0], found_antinode[1])] += 1
                        else:
                            found_antinodes[(found_antinode[0], found_antinode[1])] = 1
                    if (found_antinode[0], found_antinode[1]) in found_updated_antinodes:
                        found_updated_antinodes[(found_antinode[0], found_antinode[1])] += 1
                    else:
                        found_updated_antinodes[(found_antinode[0], found_antinode[1])] = 1
                    multiplier += 1
                else:
                    in_bound = False

            for a in found_antinodes.keys():
                if a in antinodes:
                    antinodes[a] += found_antinodes[a]
                else:
                    antinodes[a] = found_antinodes[a]
            for a in found_updated_antinodes.keys():
                if a in updated_antinodes:
                    updated_antinodes[a] += found_updated_antinodes[a]
                else:
                    updated_antinodes[a] = found_updated_antinodes[a]

s = 0
s2 = 0

s += len(antinodes)
s2 += len(updated_antinodes)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)