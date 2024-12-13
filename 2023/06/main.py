import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

times = [int(time) for time in lines[0].split(':')[1].split()]
distances = [int(distance) for distance in lines[1].split(':')[1].split()]

s = 1
s2 = 0

for time, distance in zip(times, distances):
    ways = 0
    for hold in range(time):
        speed = hold
        traveled = speed * (time - hold)
        if traveled > distance:
            ways += 1

    s *= ways

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)