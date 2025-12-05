import collections
import functools
import itertools
import json
import math
import re
import sys

import lib.aoc

def parse_input(s):
    parts = s.split('\n\n')
    map_str = parts[0]
    path_str = parts[1].strip()
    
    grid = {}
    # Don't strip map lines, leading spaces are significant for column index
    lines = map_str.splitlines()
    for r, line in enumerate(lines):
        for c, char in enumerate(line):
            if char in ('.', '#'):
                grid[(r, c)] = char
                
    instructions = []
    for match in re.findall(r'(\d+|[LR])', path_str):
        if match.isdigit():
            instructions.append(int(match))
        else:
            instructions.append(match)
            
    return grid, instructions

def get_ranges(grid):
    row_ranges = {}
    col_ranges = {}
    
    for r, c in grid:
        if r not in row_ranges: row_ranges[r] = [c, c]
        else:
            row_ranges[r][0] = min(row_ranges[r][0], c)
            row_ranges[r][1] = max(row_ranges[r][1], c)
            
        if c not in col_ranges: col_ranges[c] = [r, r]
        else:
            col_ranges[c][0] = min(col_ranges[c][0], r)
            col_ranges[c][1] = max(col_ranges[c][1], r)
            
    return row_ranges, col_ranges

def part1(s):
    grid, instructions = parse_input(s)
    row_ranges, col_ranges = get_ranges(grid)
    
    start_r = 0
    # Ensure we start on a valid row
    while start_r not in row_ranges:
        start_r += 1
        
    start_c = row_ranges[start_r][0]
    # "You begin the path in the leftmost open tile"
    while grid[(start_r, start_c)] == '#':
        start_c += 1
        
    r, c = start_r, start_c
    
    # Facing: 0=R, 1=D, 2=L, 3=U
    facing = 0 
    dr = [0, 1, 0, -1]
    dc = [1, 0, -1, 0]
    
    for instr in instructions:
        if isinstance(instr, int):
            for _ in range(instr):
                nr, nc = r + dr[facing], c + dc[facing]
                
                # Check wrap
                if (nr, nc) not in grid:
                    if facing == 0: # Right -> wrap to left (min col)
                        nc = row_ranges[r][0]
                        nr = r # r should be same
                    elif facing == 1: # Down -> wrap to top (min row)
                        nr = col_ranges[c][0]
                        nc = c # c should be same
                    elif facing == 2: # Left -> wrap to right (max col)
                        nc = row_ranges[r][1]
                        nr = r # r should be same
                    elif facing == 3: # Up -> wrap to bottom (max row)
                        nr = col_ranges[c][1]
                        nc = c # c should be same
                
                # Check wall
                if grid[(nr, nc)] == '#':
                    break
                
                r, c = nr, nc
        else:
            if instr == 'R':
                facing = (facing + 1) % 4
            elif instr == 'L':
                facing = (facing - 1) % 4
    
    answer = 1000 * (r + 1) + 4 * (c + 1) + facing
    lib.aoc.give_answer_current(1, answer)

def part2(s):
    pass

INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
