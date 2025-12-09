import collections
import functools
import itertools
import json
import math
import typing

import parse
import re2 as re
import sympy # sympy.parse_expr, sympy.solve, sympy.Eq
import sys # sys.setrecursionlimit(1000000)
import z3 # x = z3.Int('x'); x < 0; (x-1) >= 0
# z3.If(x >= 0, x, -x); z3.And(); z3.Or(); z3.Not()
# s = z3.Solver(); solver.add(constraint); s.check(); s.model()[x].as_long()
# o = z3.Optimize(); o.minimize(x); o.check(); o.model()[x].as_long()

import lib.algorithms
import lib.aoc
import lib.cyk
import lib.graph
from lib.graphics import *
import lib.grid
import lib.hex_coord
import lib.lazy_dict
import lib.math
import lib.ocr
import lib.parsing

class Blueprint(typing.NamedTuple):
    num: int
    ore_robot_ore_cost: int
    clay_robot_ore_cost: int
    obsidian_robot_ore_cost: int
    obsidian_robot_clay_cost: int
    geode_robot_ore_cost: int
    geode_robot_obsidian_cost: int

class State(typing.NamedTuple):
    ore_robots: int
    ore: int
    clay_robots: int
    clay: int
    obsidian_robots: int
    obsidian: int
    geode_robots: int
    geodes: int

    remaining_time: int

    def build(self, bp, harvest_minutes,
              ore=0, clay=0, obsidian=0, geode=0):
        remaining_time = self.remaining_time - harvest_minutes

        remaining_useful_building_cycles = remaining_time - 1

        ore_robots = self.ore_robots + ore
        ore = (self.ore
               + self.ore_robots * harvest_minutes
               - ore * bp.ore_robot_ore_cost
               - clay * bp.clay_robot_ore_cost
               - obsidian * bp.obsidian_robot_ore_cost
               - geode * bp.geode_robot_ore_cost)

        max_ore_per_robot = max(bp.ore_robot_ore_cost,
                                bp.clay_robot_ore_cost,
                                bp.obsidian_robot_ore_cost,
                                bp.geode_robot_ore_cost)

        max_ore_needed = remaining_useful_building_cycles * max_ore_per_robot
        remaining_useful_ore_harvest_cycles = remaining_useful_building_cycles - 1
        max_reserve_ore_needed = max_ore_needed - remaining_useful_ore_harvest_cycles * ore_robots
        ore = min(ore, max_reserve_ore_needed)

        return State(ore_robots,
                     ore,
                     self.clay_robots + clay,
                     self.clay + self.clay_robots * harvest_minutes - obsidian * bp.obsidian_robot_clay_cost,
                     self.obsidian_robots + obsidian,
                     self.obsidian + self.obsidian_robots * harvest_minutes - geode * bp.geode_robot_obsidian_cost,
                     self.geode_robots + geode,
                     self.geodes + self.geode_robots * harvest_minutes,
                     self.remaining_time - harvest_minutes)

    def minutes_to_build_ore_robot(self, bp):
        return max((bp.ore_robot_ore_cost - self.ore + self.ore_robots - 1) // self.ore_robots,
                   0) + 1

    def minutes_to_build_clay_robot(self, bp):
        return max((bp.clay_robot_ore_cost - self.ore + self.ore_robots - 1) // self.ore_robots,
                   0) + 1

    def minutes_to_build_obsidian_robot(self, bp):
        return max((bp.obsidian_robot_ore_cost - self.ore + self.ore_robots - 1) // self.ore_robots,
                   (bp.obsidian_robot_clay_cost - self.clay + self.clay_robots - 1) // self.clay_robots,
                   0) + 1

    def minutes_to_build_geode_robot(self, bp):
        return max((bp.geode_robot_ore_cost - self.ore + self.ore_robots - 1) // self.ore_robots,
                   (bp.geode_robot_obsidian_cost - self.obsidian + self.obsidian_robots - 1) // self.obsidian_robots,
                   0) + 1

    def minimum_guaranteed_geodes(self):
        return self.geodes + self.geode_robots * self.remaining_time

    def theoretical_maximum_geodes(self):
        if self.remaining_time <= 1:
            return self.minimum_guaranteed_geodes()

        # If we theoretically built 1 geode robot per minute until time ran
        # out this is how many more geodes we would get
        theoretical_additions = (self.remaining_time-1) * self.remaining_time // 2

        return self.minimum_guaranteed_geodes() + theoretical_additions

def max_geodes(bp, minutes):
    max_ore_needed = max(bp.clay_robot_ore_cost,
                         bp.obsidian_robot_ore_cost,
                         bp.geode_robot_ore_cost)

    best = 0

    @functools.cache
    def update_best(state):
        nonlocal best

        best = max(best, state.minimum_guaranteed_geodes())
        if state.theoretical_maximum_geodes() <= best:
            return best

        # Only try to build robots if:
        # 1) Their prerequisites are being harvested
        # 2) They are needed (as in, there aren't enough for the maximum demand yet)
        # 3) They will be complete early enough to be useful. That is, there is enough
        # time left for a new geode to potentially be harvested thanks to this robot.

        if state.ore_robots < max_ore_needed:
            # Harvest -> geode robot -> harvest
            build_minutes = state.minutes_to_build_ore_robot(bp)
            if build_minutes <= state.remaining_time-3:
                update_best(state.build(bp, build_minutes, ore=1))

        if state.clay_robots < bp.obsidian_robot_clay_cost:
            # Harvest -> obsidian robot -> harvest -> geode robot -> harvest
            build_minutes = state.minutes_to_build_clay_robot(bp)
            if build_minutes <= state.remaining_time-5:
                update_best(state.build(bp, build_minutes, clay=1))

        if state.clay_robots > 0 and state.obsidian_robots < bp.geode_robot_obsidian_cost:
            build_minutes = state.minutes_to_build_obsidian_robot(bp)
            # Harvest -> geode robot -> harvest
            if build_minutes <= state.remaining_time-3:
                update_best(state.build(bp, build_minutes, obsidian=1))

        if state.obsidian_robots > 0:
            build_minutes = state.minutes_to_build_geode_robot(bp)
            # Harvest
            if build_minutes <= state.remaining_time-1:
                update_best(state.build(bp, build_minutes, geode=1))

    update_best(State(ore_robots=1,
                      ore=0,
                      clay_robots=0,
                      clay=0,
                      obsidian_robots=0,
                      obsidian=0,
                      geode_robots=0,
                      geodes=0,
                      remaining_time=minutes))

    return best


def parse_input(s) -> list[Blueprint]:
    blueprints = []
    for line in s.splitlines():
        m = re.match(r"Blueprint (\d+): Each ore robot costs (\d+) ore. Each clay robot costs (\d+) ore. Each obsidian robot costs (\d+) ore and (\d+) clay. Each geode robot costs (\d+) ore and (\d+) obsidian.", line)

        num = int(m.group(1))
        orebot_cost_ore = int(m.group(2))
        claybot_cost_ore = int(m.group(3))
        obsidianbot_cost_ore = int(m.group(4))
        obsidianbot_cost_clay = int(m.group(5))
        geodebot_cost_ore = int(m.group(6))
        geodebot_cost_obsidian = int(m.group(7))

        blueprint = Blueprint(num, orebot_cost_ore, claybot_cost_ore, obsidianbot_cost_ore, obsidianbot_cost_clay, geodebot_cost_ore, geodebot_cost_obsidian)
        blueprints.append(blueprint)
    return blueprints

def part1(s):
    blueprints = parse_input(s)
    answer = sum((i + 1) * max_geodes(bp, 24)
                 for i, bp in enumerate(blueprints))

    lib.aoc.give_answer_current(1, answer)

def part2(s):
    blueprints = parse_input(s)
    answer = 1
    for bp in blueprints[:3]:
        answer *= max_geodes(bp, 32)
    lib.aoc.give_answer_current(2, answer)

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
