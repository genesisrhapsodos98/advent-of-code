input_file = open(".\\input.txt", "r")
input_content = input_file.read()
lines = input_content.split('\n')


def count_xmas_from_start_position(x, y, matrix):
    total = 0
    matrix_size = len(matrix)
    if matrix[x][y] == 'X':
        if y + 3 < matrix_size and matrix[x][y + 1] == 'M' and matrix[x][y + 2] == 'A' and matrix[x][y + 3] == 'S':
            total += 1
        if y - 3 >= 0 and matrix[x][y - 1] == 'M' and matrix[x][y - 2] == 'A' and matrix[x][y - 3] == 'S':
            total += 1
        if x + 3 < matrix_size and matrix[x + 1][y] == 'M' and matrix[x + 2][y] == 'A' and matrix[x + 3][y] == 'S':
            total += 1
        if x - 3 >= 0 and matrix[x - 1][y] == 'M' and matrix[x - 2][y] == 'A' and matrix[x - 3][y] == 'S':
            total += 1
        if x + 3 < matrix_size and y + 3 < matrix_size and matrix[x + 1][y + 1] == 'M' and matrix[x + 2][
            y + 2] == 'A' and matrix[x + 3][y + 3] == 'S':
            total += 1
        if x - 3 >= 0 and y + 3 < matrix_size and matrix[x - 1][y + 1] == 'M' and matrix[x - 2][y + 2] == 'A' and \
                matrix[x - 3][y + 3] == 'S':
            total += 1
        if x + 3 < matrix_size and y - 3 >= 0 and matrix[x + 1][y - 1] == 'M' and matrix[x + 2][y - 2] == 'A' and \
                matrix[x + 3][y - 3] == 'S':
            total += 1
        if x - 3 >= 0 and y - 3 >= 0 and matrix[x - 1][y - 1] == 'M' and matrix[x - 2][y - 2] == 'A' and matrix[x - 3][
            y - 3] == 'S':
            total += 1
    return total


def count_cross_mas_from_start_position(x, y, matrix):
    total = 0
    matrix_size = len(matrix)
    if matrix[x][y] == 'A' and x - 1 >= 0 and y - 1 >= 0 and x + 1 < matrix_size and y + 1 < matrix_size:
        valid_forward_diagonal = (matrix[x - 1][y - 1] == 'M' and matrix[x + 1][y + 1] == 'S') or (
                    matrix[x - 1][y - 1] == 'S' and matrix[x + 1][y + 1] == 'M')
        valid_backward_diagonal = (matrix[x - 1][y + 1] == 'M' and matrix[x + 1][y - 1] == 'S') or (
                    matrix[x - 1][y + 1] == 'S' and matrix[x + 1][y - 1] == 'M')
        if valid_backward_diagonal and valid_forward_diagonal:
            total += 1
    return total


matrix = lines
s = 0
s2 = 0
for x in range(len(matrix)):
    for y in range(len(matrix)):
        c = count_xmas_from_start_position(x, y, matrix)
        cx = count_cross_mas_from_start_position(x, y, matrix)
        s += c
        s2 += cx

print(s)
print(s2)
