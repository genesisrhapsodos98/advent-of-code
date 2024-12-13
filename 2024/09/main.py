import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

def build_line(disk_map):
    line = []
    block_num = 0
    for idx, elem in enumerate(disk_map):
        if idx % 2 == 0:
            next_elem = str(block_num)
            block_num += 1
        else:
            next_elem = '.'
        for i in range(int(elem)):
            line.append(next_elem)
    return line

def build_line_map(line):
    count = 1
    current_elem = None
    line_map = []
    for idx, elem in enumerate(line):
        if elem != current_elem:
            if current_elem is not None:
                line_map.append((current_elem, count))
            current_elem = elem
            count = 1
        else:
            count += 1
    line_map.append((current_elem, count))
    return line_map

def calculate_checksum(line):
    checksum = 0
    for idx, elem in enumerate(line):
        if elem == '.':
            continue
        checksum += idx * int(elem)
    return checksum

line = build_line(lines[0])
original_line = line[:]

end_idx = len(line) - 1
for i in range(len(line)):
    if line[i] != '.':
        continue
    for j in range(end_idx, i, -1):
        if line[j] == '.':
            continue
        line[i] = line[j]
        line[j] = '.'
        end_idx = j
        break

s = 0
s2 = 0

s = calculate_checksum(line)
line_map = build_line_map(original_line)

attempted_files = []
i = len(line_map) - 1
while i >= 0:
    elem, amount = line_map[i]
    if elem == '.':
        i -= 1
        continue
    file = int(elem)
    if file in attempted_files:
        i -= 1
        continue
    attempted_files.append(file)

    found = False
    for j in range(i):
        space_elem, space_amount = line_map[j]
        if space_elem != '.' or space_amount < amount:
            continue
        found = True
        line_map[j] = (space_elem, space_amount - amount)
        line_map.insert(j, (elem, amount))

        new_amount = amount
        new_index = i + 1
        if new_index + 1 < len(line_map) and line_map[new_index + 1][0] == '.':
            new_amount += line_map[new_index + 1][1]
            del line_map[new_index + 1]
        if new_index - 1 >= 0 and line_map[new_index - 1][0] == '.':
            new_amount += line_map[new_index - 1][1]
            del line_map[new_index - 1]
            new_index -= 1
        line_map[new_index] = ('.', new_amount)
        if space_amount == amount:
            if new_index != j + 1:
                del line_map[j + 1]
                new_index -= 1
        i = new_index - 1
        break
    if not found:
        i -= 1

line = []
for item in line_map:
    elem, amount = item
    for i in range(amount):
        line.append(elem)

s2 = calculate_checksum(line)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)

