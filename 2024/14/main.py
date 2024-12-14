import lib.aoc

input_content = lib.aoc.get_current_input()

# input_content = """p=0,4 v=3,-3
# p=6,3 v=-1,-3
# p=10,3 v=-1,2
# p=2,0 v=2,-1
# p=0,0 v=1,3
# p=3,0 v=-2,-2
# p=7,6 v=-1,-3
# p=3,0 v=-1,-2
# p=9,3 v=2,3
# p=7,3 v=-1,2
# p=2,4 v=2,-3
# p=9,5 v=-3,-3"""

lines = input_content.split('\n')

width = 101
height = 103

# width = 11
# height = 7

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


lib.aoc.give_answer_current(1, s)
# lib.aoc.give_answer_current(2, s2)