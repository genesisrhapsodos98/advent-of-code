import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

separator_index = lines.index('')
first_section = lines[:separator_index]
second_section = lines[separator_index + 1:]

rules = [rule.split('|') for rule in first_section]
instructions = [instruction.split(',') for instruction in second_section]


def is_correct_update(rules, instruction):
    for first_idx in range(len(instruction)):
        relevant_rules = [rule for rule in rules if rule[1] == instruction[first_idx]]
        for second_idx in range(first_idx + 1, len(instruction)):
            relevant_rules_2 = [rule for rule in relevant_rules if rule[0] == instruction[second_idx]]
            if (len(relevant_rules_2) > 0):
                return False

    return True


def do_correct_update(rules, instruction):
    relevant_rules = [rule for rule in rules if rule[0] in instruction or rule[1] in instruction]

    while not is_correct_update(rules, instruction):
        for first_idx in range(len(instruction)):
            for second_idx in range(first_idx + 1, len(instruction)):
                offended_rules = [rule for rule in relevant_rules if
                                  rule[0] == instruction[second_idx] and rule[1] == instruction[first_idx]]
                if len(offended_rules) > 0:
                    tmp = instruction[first_idx]
                    instruction[first_idx] = instruction[second_idx]
                    instruction[second_idx] = tmp

    return instruction


def get_middle_value(instruction):
    return int(instruction[len(instruction) // 2])


s = 0
s2 = 0
for instruction in instructions:
    if is_correct_update(rules, instruction):
        s += get_middle_value(instruction)
    else:
        new_instruction = do_correct_update(rules, instruction)
        s2 += get_middle_value(new_instruction)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)
