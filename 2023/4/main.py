import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

cards = []

def calculate_point(card):
    winning_numbers, your_numbers = card

    your_winning_numbers = [num for num in your_numbers if num in winning_numbers]
    return 2 ** (len(your_winning_numbers) - 1) if len(your_winning_numbers) > 0 else 0

for line in lines:
    card = line.split(':')[1]
    [left, right] = card.split('|')
    left_numbers = [int(num.strip()) for num in left.split(' ') if num != '']
    right_numbers = [int(num.strip()) for num in right.split(' ') if num != '']

    cards.append((left_numbers, right_numbers))

s = 0
s2 = 0

for card in cards:
    s += calculate_point(card)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)