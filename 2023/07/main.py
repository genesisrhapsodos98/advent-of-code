from collections import Counter

import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

cards = '23456789TJQKA'

def strength(hand):
    card_count = Counter()
    high_cards = [cards.index(c) for c in hand]
    for card in hand:
        card_count[card] += 1

    if 5 in card_count.values():
        return 7, high_cards
    if 4 in card_count.values():
        return 6, high_cards
    if 3 in card_count.values() and 2 in card_count.values():
        return 5, high_cards
    if 3 in card_count.values():
        return 4, high_cards
    if len(list(filter(lambda x: x == 2, card_count.values()))) == 2:
        return 3, high_cards
    if 2 in card_count.values():
        return 2, high_cards
    return 1, high_cards


hands = []
bids = []

for line in lines:
    hand, bid = line.split(' ')
    hands.append(hand)
    bids.append(int(bid))

s = 0
s2 = 0

group = list(zip(hands, bids, [strength(h) for h in hands]))
group.sort(key=lambda x: (x[2][0], x[2][1][0], x[2][1][1], x[2][1][2], x[2][1][3], x[2][1][4], ))
print(group[0][0], group[0][2])
print(group[-1][0], group[-1][2])

for rank, (_, bid, (_, _)) in enumerate(group, 1):
    s += rank * bid

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)