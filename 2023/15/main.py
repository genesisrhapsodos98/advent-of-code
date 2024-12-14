from collections import defaultdict

import lib.aoc

input_content = lib.aoc.get_current_input()
segments = input_content.split(',')

def hash_value(s: str):
    cur = 0
    for code in s.encode('ascii'):
        cur += code
        cur *= 17
        cur %= 256
    return cur

s = 0
s2 = 0

def focusing_power(boxes):
    power = 0
    for idx, box in boxes.items():
        for lens_idx, lens in enumerate(box):
            _, focal_length = lens
            lens_power = 1 + idx
            lens_power *= 1 + lens_idx
            lens_power *= focal_length

            power += lens_power
    return power

boxes = defaultdict(list)

for segment in segments:
    s += hash_value(segment)

    if '=' in segment:
        op = '='
        [label, focal_length] = segment.split('=')
    else:
        op = '-'
        [label, _] = segment.split('-')

    box_idx = hash_value(label)
    box = boxes[box_idx]

    if op == '=':
        new_lens = (label, int(focal_length))
        found_old_lens = False
        for idx, lens in enumerate(box):
            l, f = lens
            if l == label:
                box[idx] = new_lens
                found_old_lens = True
                break
        if not found_old_lens:
            box.append(new_lens)
    else:
        found_existing_lens = False
        for idx, lens in enumerate(box):
            l, f = lens
            if l == label:
                box.pop(idx)
                break

s2 = focusing_power(boxes)


lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)