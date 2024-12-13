import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

map_height = len(lines)
map_width = len(lines[0])

def add_coordinates(coords, offset):
    x, y = coords
    ox, oy = offset
    return (x + ox, y + oy)

def in_bounds(coords):
    x, y = coords
    return 0 <= x < map_width and 0 <= y < map_height


def get_value(coords):
    x, y = coords
    return lines[y][x]


def flood_fill(coords):
    result = []
    visited_coords = {}
    crop = get_value(coords)

    queue = [coords]
    while len(queue) > 0:
        current_position = queue.pop(0)
        current_crop = get_value(current_position)
        if current_crop != crop or current_position in result:
            continue
        result.append(current_position)
        for offset in adjacent_offsets:
            new_position = add_coordinates(current_position, offset)
            if not in_bounds(new_position) or new_position in visited_coords:
                continue
            queue.append(new_position)
            visited_coords[current_position] = True
    return result


def calculate_perimeter(region):
    region_perimeter = 0
    for plot in region:
        for offset in adjacent_offsets:
            new_position = add_coordinates(plot, offset)
            region_perimeter += new_position not in region
    return region_perimeter


def calculate_discount_perimeter(region):
    sides = 0
    # Number of sides = number of corners
    for (x, y) in region:
        # Outer corners
        sides += (x - 1, y) not in region and (x, y - 1) not in region
        sides += (x + 1, y) not in region and (x, y - 1) not in region
        sides += (x - 1, y) not in region and (x, y + 1) not in region
        sides += (x + 1, y) not in region and (x, y + 1) not in region
        # Inner corners
        sides += (x - 1, y) in region and (x, y - 1) in region and (x - 1, y - 1) not in region
        sides += (x + 1, y) in region and (x, y - 1) in region and (x + 1, y - 1) not in region
        sides += (x - 1, y) in region and (x, y + 1) in region and (x - 1, y + 1) not in region
        sides += (x + 1, y) in region and (x, y + 1) in region and (x + 1, y + 1) not in region
    return sides


visited = {}
regions = []

adjacent_offsets = [(-1, 0), (1, 0), (0, -1), (0, 1)]

s = 0
s2 = 0

for i in range(map_height):
    for j in range(map_width):
        if (j, i) in visited:
            continue
        region = flood_fill((j, i))
        regions.append(region)
        for pos in region:
            visited[pos] = True

for region in regions:
    area = len(region)
    perimeter = calculate_perimeter(region)
    discount_perimeter = calculate_discount_perimeter(region)
    s += area * perimeter
    s2 += area * discount_perimeter

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)
