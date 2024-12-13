import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

digits = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']
digit_texts = ['one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight', 'nine']

s = 0
s2 = 0

for line in lines:
    left_index = len(line)
    right_index = -1

    left_result = 0
    right_result = 0

    for digit in digits:
        if digit in line:
            li = line.index(digit)
            ri = line.rfind(digit)

            if li < left_index:
                left_index = li
                left_result = int(digit)
            if ri > right_index:
                right_index = ri
                right_result = int(digit)

    s += left_result * 10 + right_result

    for value, text in enumerate(digit_texts, 1):
        if text in line:
            li = line.index(text)
            ri = line.rfind(text)

            if li < left_index:
                left_index = li
                left_result = value
            if ri > right_index:
                right_index = ri
                right_result = value

    s2 += left_result * 10 + right_result

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)
