import datetime
import os
import subprocess
import sys
import time

import lib.aoc
def error_exit(msg):
    print(msg)
    os.system('pause')
    sys.exit(-1)
def open_editor(path):
    # Opens the PyCharm editor for the path requested. This is done with a
    # separate command window so that when this program closes its command
    # window can cleanly disappear
    subprocess.Popen(['start', 'cmd', '/c', 'editor.bat', path],
                     shell=True)
def get_template(year, day):
    part_1_template = f'''def part1(s):
    _ = parse_input(s)
    answer = 0
    lib.aoc.give_answer_current(1, answer)'''
    if year >= 2025 and day == 12:
        part_2_template = f'''def part2(s):
    print('Is there a part 2? Unsure until we see it!')
    lib.aoc.give_answer_current(2, 1) # Allow quick submission in case there's no part 2
##    print(f'The answer to part two is {{answer}}')
##    lib.aoc.give_answer_current(2, answer)'''
    elif day == 25:
        part_2_template = f'''def part2(s):
    print('There is no part two for Christmas!')'''
    else:
        part_2_template = f'''def part2(s):
    pass
    _ = parse_input(s)
    answer = 0
    # lib.aoc.give_answer_current(2, answer)'''
    return f'''import collections
import functools
import itertools
import json
import math
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

def parse_input(s):
    # nums = list(map(lambda r:r[0], parse.findall('{{:d}}', s)))
    # lines = s.splitlines()
    # groups = s.split('\\n\\n')
    # grid = lib.grid.FixedGrid.parse(s, value_fn=int)
    # grid = lib.grid.FixedGrid.parse(s,
    #                                linesplit_fn=lambda line: line.split(),
    #                                value_fn=int)
    return None

{part_1_template}

{part_2_template}

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
'''

try:
    year = int(input('Year ("warmup" for warmup): '))
    if year == 'warmup':
        day = int(input('Day: '))
        if day not in range(1, 26):
            error_exit(f'Advent of code runs from December 1st through 25th. Day {day} is invalid')
        previous_solutions = {}
        year = 2015
        while True:
            if day > 12 and year >= 2025:
                # Starting in 2025 there are only 12 days
                break

            time_to_release = lib.aoc.time_to_release(year, day)
            if time_to_release > datetime.timedelta(days=-1):
                # This is a future (or current) problem!
                break
            if not lib.aoc.knows_solutions_for(year, day):
                year += 1
                continue
            if input(f'Warm up with {year} Day {day}? ').lower() in ('y', 'yes', '1'):
                path = f'{year}/{day:02}/main.py'
                if os.path.exists(path):
                    with open(path, 'rb') as f:
                        previous_solutions[year] = f.read()
                os.makedirs(os.path.split(path)[0], exist_ok=True)
                with open(path, 'w+') as f:
                    f.write(get_template(year, day))
                lib.aoc.ensure_valid_session_cookie()
                open_editor(path)

                time.sleep(5)
                lib.aoc.open_pages_for(year, day)
            year += 1
        print('Finished with warmups. Waiting to restore old solutions...')
        os.system('pause')
        for year, old_solution in previous_solutions.items():
            path = f'{year}/{day:02}/solution.py'
            with open(path, 'wb') as f:
                f.write(old_solution)
    else:
        year = int(year)
        if year < 2015:
            error_exit(f'Advent of Code started in 2015! Year {year} is invalid')

        day = int(input('Day: '))
        print(year, day)
        if year < 2025 and day not in range(1, 26):
            error_exit(f'Advent of code runs from December 1st through 25th. Day {day} is invalid')
        elif year >= 2025 and day not in range(1, 13):
            error_exit(f'Advent of code runs from December 1st through 12th starting in 2025. Day {day} is invalid')
        time_to_release = lib.aoc.time_to_release(year, day)
        if time_to_release >= datetime.timedelta(days=1):
            error_exit(f'{year} Day {day} is more than a day in the future!')

        path = f'{year}/{day:02}/main.py'

        if not os.path.exists(path):
            print(f'Writing template for {year} Day {day}')
            os.makedirs(os.path.split(path)[0], exist_ok=True)
            with open(path, 'w+') as f:
                f.write(get_template(year, day))

        open_editor(path)

        lib.aoc.ensure_valid_session_cookie()

        if time_to_release <= datetime.timedelta(days=-1):
            print(f'{year} Day {day} is more than a day in the past!')
            if input('Begin time trial? ').lower() in ('y', 'yes', '1'):
                lib.aoc.begin_time_trial(year, day)
        else:
            lib.aoc.download_input_when_live(year, day)
except SystemExit:
    raise
except:
    import traceback
    traceback.print_exc()
    error_exit('Unhandled exception')