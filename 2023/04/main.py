from collections import Counter

import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

cards = []

def calculate_point(card):
    matching_numbers = count_matching_numbers(card)
    return 2 ** (matching_numbers - 1) if matching_numbers > 0 else 0

def count_matching_numbers(card):
    winning_numbers, your_numbers = card

    your_winning_numbers = [num for num in your_numbers if num in winning_numbers]
    return len(your_winning_numbers)

for line in lines:
    card = line.split(':')[1]
    [left, right] = card.split('|')
    left_numbers = [int(num.strip()) for num in left.split(' ') if num != '']
    right_numbers = [int(num.strip()) for num in right.split(' ') if num != '']

    cards.append((left_numbers, right_numbers))

s = 0
s2 = 0

copies = Counter()
for i in range(len(cards)):
    copies[i] += 1

for idx, card in enumerate(cards):
    s += calculate_point(card)
    matching_numbers = count_matching_numbers(card)
    current_copies = copies[idx]
    for i in range(matching_numbers):
        copies[idx + i + 1] += current_copies

s2 = sum(c for c in copies.values())

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)