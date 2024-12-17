import lib.aoc

input_content = lib.aoc.get_current_input()

lines = input_content.split('\n')

width = 101
height = 103

def next_turn(robot):
    p, v = robot
    px, py = p
    vx, vy = v
    new_p = (px + vx) % width, (py + vy) % height
    return new_p, v

robots = []

for line in lines:
    [left, right] = line.split()
    px, py = list(map(int, left.split('=')[1].split(',')))
    vx, vy = list(map(int, right.split('=')[1].split(',')))

    robots.append(((px, py), (vx, vy)))


original_robots = robots[:]

s = 0
s2 = 0

for i in range(100):
    for idx, robot in enumerate(robots):
        robots[idx] = next_turn(robot)

mid_x = width // 2
mid_y = height // 2

q1, q2, q3, q4 = 0, 0, 0, 0

q1 += sum(1 for (px, py), v in robots if 0 <= px < mid_x and 0 <= py < mid_y)
q2 += sum(1 for (px, py), v in robots if mid_x < px < width and 0 <= py < mid_y)
q3 += sum(1 for (px, py), v in robots if 0 <= px < mid_x and mid_y < py < height)
q4 += sum(1 for (px, py), v in robots if mid_x < px < width and mid_y < py < height)

s += q1 * q2 * q3 * q4

robots = original_robots

while True:
    for idx, robot in enumerate(robots):
        robots[idx] = next_turn(robot)
    s2 += 1

    # Very dumb idea but it works
    # Find the first time every robot is on a unique position
    # Because if robots are overlapping they won't form a picture
    pos = [robot[0] for robot in robots]
    if len(pos) == len(set(pos)):
        break

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)