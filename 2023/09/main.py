import lib.aoc

input_content = lib.aoc.get_current_input()
lines = input_content.split('\n')

sequences = []

for line in lines:
    sequences.append(list(map(int, line.split())))

def extrapolate(sequence):
    seqs = [sequence]
    current_sequence = sequence
    while True:
        current_sequence = diff(current_sequence)
        seqs.append(current_sequence)
        if all([x == 0 for x in current_sequence]):
            break

    current = 0
    for seq in seqs[-1::-1]:
        current = seq[-1] + current

    return current

def reverse_extrapolate(sequence):
    seqs = [sequence]
    current_sequence = sequence
    while True:
        current_sequence = diff(current_sequence)
        seqs.append(current_sequence)
        if all([x == 0 for x in current_sequence]):
            break

    current = 0
    for seq in seqs[-1::-1]:
        current = seq[0] - current

    return current

def diff(sequence):
    result = []
    for i in range(len(sequence) - 1):
        result.append(sequence[i + 1] - sequence[i])
    return result

s = 0
s2 = 0

for seq in sequences:
    s += extrapolate(seq)
    s2 += reverse_extrapolate(seq)

lib.aoc.give_answer_current(1, s)
lib.aoc.give_answer_current(2, s2)