import lib.aoc
import lib.graph
import lib.grid

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

def resolve_instruction(match):
    opp, instruction = match.split()
    opp_choice = 'ABC'.index(opp)
    result_score = {'X': 0, 'Y': 3, 'Z': 6}[instruction]
    if instruction == 'X':
        player_choice = (opp_choice + 2) % 3
    elif instruction == 'Y':
        player_choice = opp_choice
    else:
        player_choice = (opp_choice + 1) % 3
    player_score = player_choice + 1
    return result_score + player_score


def part1(s):
    matches = parse_input(s)
    answer = 0
    for match in matches:
        answer += resolve_match(match)
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    matches = parse_input(s)
    answer = 0
    for match in matches:
        answer += resolve_instruction(match)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
