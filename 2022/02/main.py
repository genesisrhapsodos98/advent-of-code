import collections
import functools
import itertools
import math
import re
import lib.aoc
import lib.graph
import lib.grid
from lib.graphics import *

def parse_input(s):
    matches = s.splitlines()
    return matches

def resolve_match(match):
    opp, player = match.split()
    opp_choice = 'ABC'.index(opp)
    player_choice = 'XYZ'.index(player)
    player_score = player_choice + 1
    result_score = {0: 3, 1: 6, 2: 0}[(player_choice - opp_choice) % 3]
    return player_score + result_score

def part1(s):
    matches = parse_input(s)
    answer = 0
    for match in matches:
        answer += resolve_match(match)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass
    _ = parse_input(s)
    answer = 0
    # lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
