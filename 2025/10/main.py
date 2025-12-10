import z3
import lib.aoc

def parse_line(line: str):
    line = line.strip()

    diagram, *button_definitions, joltage_definition = line.split(' ')

    pattern = diagram[1:-1]
    n_lights = len(pattern)
    target_bits = [1 if c == '#' else 0 for c in pattern]

    buttons = []
    for bd in button_definitions:
        bd = bd[1:-1]
        indices = list(map(int, bd.split(',')))
        buttons.append(indices)

    joltage_definition = joltage_definition[1:-1]
    jolts = list(map(int, joltage_definition.split(',')))

    return n_lights, target_bits, buttons, jolts

def min_presses_lights(n_lights, target_bits, buttons):
    m = len(buttons)

    opt = z3.Optimize()
    presses = [z3.Int(f"presses{j}") for j in range(m)]
    for var in presses:
        opt.add(var >= 0)

    for c in range(n_lights):
        involved = [j for j, indices in enumerate(buttons) if c in indices]
        if involved:
            rem = target_bits[c]
            opt.add(sum(presses[j] for j in involved) % 2 == rem)
        else:
            opt.add(target_bits[c] == 0)

    total_presses = sum(presses)
    opt.minimize(total_presses)

    assert opt.check() == z3.sat

    model = opt.model()
    return sum(model[var].as_long() for var in presses)

def min_presses_jolts(jolts, buttons):
    diagram_length = len(jolts)
    m = len(buttons)

    opt = z3.Optimize()
    presses = [z3.Int(f"presses{j}") for j in range(m)]
    for var in presses:
        opt.add(var >= 0)

    for diagram_index in range(diagram_length):
        involved_buttons = [
            button_index for button_index, button_target_indices in enumerate(buttons)
            if diagram_index in button_target_indices
        ]
        if involved_buttons:
            opt.add(sum(presses[button_index] for button_index in involved_buttons) == jolts[diagram_index])
        else:
            opt.add(jolts[diagram_index] == 0)

    total_presses = sum(presses)
    opt.minimize(total_presses)

    assert opt.check() == z3.sat

    model = opt.model()
    return sum(model[var].as_long() for var in presses)


def part1(s: str):
    answer = 0
    for line in s.splitlines():
        parsed = parse_line(line)
        n_lights, target_bits, buttons, _ = parsed
        presses = min_presses_lights(n_lights, target_bits, buttons)
        answer += presses
    lib.aoc.give_answer_current(1, answer)


def part2(s: str):
    answer = 0
    for line in s.splitlines():
        parsed = parse_line(line)
        _, _, buttons, jolts = parsed
        presses = min_presses_jolts(jolts, buttons)
        answer += presses
    lib.aoc.give_answer_current(2, answer)


INPUT = lib.aoc.get_current_input()
part1(INPUT)
part2(INPUT)
