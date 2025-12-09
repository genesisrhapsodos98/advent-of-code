import lib.aoc
from lib.grid import FixedGrid

input_content = lib.aoc.get_current_input()
grid = FixedGrid.parse(input_content)

def flood_fill(coords):
    result = []
    visited_coords = {}
    crop = grid[coords]

    queue = [coords]
    while len(queue) > 0:
        current_position = queue.pop(0)
        x, y = current_position
        current_crop = grid[current_position]
        if current_crop != crop or current_position in result:
            continue
        result.append(current_position)
        neighbors = grid.neighbors(x, y)
        for neighbor in neighbors:
            if neighbor in visited_coords:
                continue
            queue.append(neighbor)
            visited_coords[neighbor] = True
    return result


def calculate_perimeter(region):
    region_perimeter = 0
    for plot in region:
        x, y = plot
        for dx, dy in adjacent_offsets:
            new_position = (x + dx, y + dy)
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


visited = set()
regions = []

adjacent_offsets = [(-1, 0), (1, 0), (0, -1), (0, 1)]

s = 0
s2 = 0

for coords, v in grid.items():
        if coords in visited:
            continue
        region = flood_fill(coords)
        regions.append(region)
        for pos in region:
            visited.add(pos)

for region in regions:
    area = len(region)
    perimeter = calculate_perimeter(region)
    discount_perimeter = calculate_discount_perimeter(region)
    s += area * perimeter
    s2 += area * discount_perimeter

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)
