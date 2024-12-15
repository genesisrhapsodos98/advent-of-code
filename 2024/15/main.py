import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
# input_content = \
# """##########
# #..O..O.O#
# #......O.#
# #.OO..O.O#
# #..O@..O.#
# #O#..O...#
# #O..O..O.#
# #.OO.O.OO#
# #....O...#
# ##########
#
# <vv>^<v^>v>^vv^v>v<>v^v<v<^vv<<<^><<><>>v<vvv<>^v^>^<<<><<v<<<v^vv^v>^
# vvv<<^>^v^^><<>>><>^<<><^vv^^<>vvv<>><^^v>^>vv<>v<<<<v<^v>^<^^>>>^<v<v
# ><>vv>v^v^<>><>>>><^^>vv>v<^^^>>v^v^<^^>v^^>v^<^v>v<>>v^v^<v>v^^<^^vv<
# <<v<^>>^^^^>>>v^<>vvv^><v<<<>^^^vv^<vvv>^>v<^^^^v<>^>vvvv><>>v^<<^^^^^
# ^><^><>>><>^^<<^^v>>><^<v>^<vv>>v>>>^v><>^v><<<<v>>v<v<v>vvv>^<><<>^><
# ^>><>^v<><^vvv<^^<><v<<<<<><^v<<<><<<^^<v<^^^><^>>^<v^><<<^>>^v<v^v<v^
# >^>>^v>vv>^<<^v<>><<><<v<<v><>v<^vv<<<>^^v^>^^>>><<^v>>v^v><^^>>^<>vv^
# <><^^>^^^<><vvvvv^v<v<<>^v<v>v<<^><<><<><<<^^<<<^<<>><<><^^^>^^<>^>v<>
# ^^>vv<^v^v<vv>^<><v<^v>^^^>>>^^vvv^>vvv<>>>^<^>>>>>^<<^v>^vvv<>^<><<v>
# v^^>>><<^^<>>^v^<v^vv<>v^<<>^<^v^v><^<<<><<^<v><v<>vv>>v><v^<vv<>v^<<^"""

# input_content = \
# """########
# #..O.O.#
# ##@.O..#
# #...O..#
# #.#.O..#
# #...O..#
# #......#
# ########
#
# <^^>>>vv<v>>v<<"""

grid_content, movements_content = input_content.split('\n\n')
movements = ''.join(movements_content.split('\n'))
grid = FixedGrid.parse(grid_content)

s = 0
s2 = 0

x, y = grid.find("@")
grid[x, y] = '.'
moves = {
    '<': (-1, 0),
    '^': (0, -1),
    '>': (1, 0),
    'v': (0, 1)
}

for move in movements:
    # grid.print()
    dx, dy = moves[move]
    nx, ny = x + dx, y + dy

    if (nx, ny) not in grid or grid[nx, ny] == '#':
        continue

    if grid[nx, ny] == '.':
        x, y = nx, ny
        continue

    if grid[nx, ny] == 'O':
        px, py = nx, ny
        while grid[px, py] == 'O':
            px, py = px + dx, py + dy

        if grid[px, py] == '#':
            continue

        while (px, py) != (nx, ny):
            grid[px, py] = 'O'
            px, py = px - dx, py - dy

        grid[nx, ny] = '.'
        x, y = nx, ny

def eval_grid(grid):
    boxes_pos = [coord for coord, value in grid.items() if value == 'O']
    answer = 0
    for x, y in boxes_pos:
        answer += 100 * y +  x
    return answer

s = eval_grid(grid)
grid.print()

# assert s == 10092, f'{s} is not 10092'
# assert s == 2028, f'{s} is not 2028'

lib.aoc.give_answer_current(1, s)
# lib.aoc.give_answer_current(2, s2)