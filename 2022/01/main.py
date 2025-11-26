import heapq
import lib.aoc
import lib.graph
import lib.grid

def parse_input(s):
    groups = s.split('\n\n')

    elves = [[int(n) for n in group.splitlines()] for group in groups]
    return elves

def part1(s):
    elves = parse_input(s)
    answer = max([sum(elf) for elf in elves])
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    elves = parse_input(s)
    calories = [sum(elf) for elf in elves]
    top3 = heapq.nlargest(3, calories)
    answer = sum(top3)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
