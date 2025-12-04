import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

times = [int(time) for time in lines[0].split(':')[1].split()]
distances = [int(distance) for distance in lines[1].split(':')[1].split()]

s = 1
s2 = 0

def solve(time, distance):
    min = 0
    max = time

    travelled = 0
    while travelled <= distance:
        min += 1
        travelled = min * (time - min)

    travelled = 0
    while travelled <= distance:
        max -= 1
        travelled = max * (time - max)

    return max - min + 1

for time, distance in zip(times, distances):
    s *= solve(time, distance)

time2 = int(''.join([str(time) for time in times]))
distance2 = int(''.join([str(distance) for distance in distances]))

s2 = solve(time2, distance2)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)