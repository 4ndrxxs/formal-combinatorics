"""Compare the predicted determinant total in every sign class with exact determinants."""

from fractions import Fraction
from math import comb

from check_conference import determinant, paley


def paley_nine():
    """Use F_3[t]/(t²+1), writing a+bt as a+3b."""
    def square(x):
        a, b = x % 3, x // 3
        return (a*a-b*b) % 3 + 3*((2*a*b) % 3)

    def subtract(x, y):
        return (x % 3-y % 3) % 3 + 3*((x//3-y//3) % 3)

    squares = {square(x) for x in range(1, 9)}
    assert len(squares) == 4
    matrix = [[0 if i == j else 1 if 9 in (i, j) or subtract(i, j) in squares else -1
               for j in range(10)] for i in range(10)]
    for i, row in enumerate(matrix):
        for j, other in enumerate(matrix):
            assert matrix[i][j] == matrix[j][i]
            assert sum(a*b for a, b in zip(row, other)) == 9*(i == j)
    return matrix


def exact_totals(c):
    n = len(c)
    counts = [0]*(n+1)
    totals = [0]*(n+1)
    for mask in range(1 << n):
        matrix = [row.copy() for row in c]
        for j, row in enumerate(matrix):
            row[j] = 1 if mask & (1 << j) else -1
        k = mask.bit_count()
        value = determinant(matrix)
        assert (-1)**(n//2)*value > 0
        counts[k] += 1
        totals[k] += abs(value)
    assert counts == [comb(n, j) for j in range(n+1)]
    return totals


def predict(q):
    v = (q+1)//2
    coeffs = [1]
    for _ in range(v):
        result = [0]*(len(coeffs)+2)
        for j, x in enumerate(coeffs):
            for offset, a in enumerate((q-1, 2*(q+1), q-1)):
                result[j+offset] += a*x
        coeffs = result
    return coeffs


def main():
    for q, c in ((5, paley(5)), (9, paley_nine()), (13, paley(13))):
        totals = exact_totals(c)
        assert totals == predict(q)
        n = q+1
        v = n//2
        assert sum(totals) == 2**n*q**v
        balanced = Fraction(totals[v], comb(n, v))
        assert balanced == sum(Fraction(comb(v,j)**2*q**(v-j), comb(2*v,2*j))
                               for j in range(v+1))
        ratio = balanced / ((2*n-2)*(n-2)**(v-1))
        print(f'Order {n}: {2**n} exact completions, {n+1} sign classes, balanced mean / W = {ratio}.')


if __name__ == '__main__':
    main()
