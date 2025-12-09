import collections
import functools

import lib.aoc
import lib.graph
import lib.grid


def parse_input(s):
    lines = s.splitlines()
    numbers = list(map(int, lines))
    return numbers


@functools.cache
def mix(num, val):
    return val ^ num


@functools.cache
def prune(num):
    return num % 16777216


@functools.cache
def randomize(seed):
    result = prune(mix(seed, seed * 64))
    result = prune(mix(result, result // 32))
    result = prune(mix(result, result * 2048))
    return result


def part1(s):
    numbers = parse_input(s)
    answer = 0

    for num in numbers:
        final = num
        for _ in range(2000):
            final = randomize(final)
        answer += final
    lib.aoc.give_answer_current(1, answer)


def get_prices(num):
    prices = [num % 10]
    current_value = num
    for _ in range(2000):
        current_value = randomize(current_value)
        prices.append(current_value % 10)
    return prices


def part2(s):
    numbers = parse_input(s)

    total_pattern_profit = collections.Counter()
    prices = [get_prices(num) for num in numbers]

    for price in prices:
        num_pattern_profit = collections.Counter()
        price_deltas = [b - a for a, b in zip(price, price[1:])]

        for i in range(len(price)):
            if i + 4 >= len(price_deltas):
                continue
            key = tuple(price_deltas[i + dd] for dd in range(4))
            if key in num_pattern_profit:
                continue
            num_pattern_profit[key] += price[i + 4]
        total_pattern_profit += num_pattern_profit

    answer = max(total_pattern_profit.values())
    print(answer)

    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
