input_file = open(".\\input.txt", "r")
input_content = input_file.read()
lines = input_content.split('\n')

rules = [line.split(' ') for line in lines]
rules = [list(map(int, rule)) for rule in rules]


def is_safe(rule):
    a = rule[:]
    b = rule[:]
    a.sort()
    b.sort(reverse=True)
    if rule != a and rule != b:
        return False
    for i in range(len(rule) - 1):
        diff = abs(rule[i] - rule[i + 1])
        if diff < 1 or diff > 3:
            return False
    return True


def is_safe_with_dampener(rule):
    if is_safe(rule):
        return True

    for i in range(len(rule)):
        new_rule = rule[:i] + rule[i + 1:]
        if is_safe(new_rule):
            return True

    return False


safe_rules = [rule for rule in rules if is_safe(rule)]
safe_rules_with_dampener = [rule for rule in rules if is_safe_with_dampener(rule)]

print(len(safe_rules))
print(len(safe_rules_with_dampener))
