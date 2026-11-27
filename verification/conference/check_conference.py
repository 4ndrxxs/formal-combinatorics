"""Check the conference block formulas with integer arithmetic and test the log bounds."""

from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import combinations
from random import Random


def determinant(matrix):
    """Fraction-free Gaussian elimination with row pivoting."""
    a = [row.copy() for row in matrix]
    divisor = 1
    sign = 1
    for j in range(len(a) - 1):
        pivot = next((r for r in range(j, len(a)) if a[r][j]), None)
        if pivot is None:
            return 0
        if j != pivot:
            a[j], a[pivot] = a[pivot], a[j]
            sign = -sign
        for r in range(j + 1, len(a)):
            for c in range(j + 1, len(a)):
                numerator = a[j][j] * a[r][c] - a[r][j] * a[j][c]
                quotient, remainder = divmod(numerator, divisor)
                assert remainder == 0
                a[r][c] = quotient
        divisor = a[j][j]
    return sign * a[-1][-1]


def paley(prime):
    """Symmetric Paley conference matrix on the field elements and infinity."""
    residues = {a * a % prime for a in range(1, prime)}
    points = range(prime + 1)

    def entry(i, j):
        if i == j:
            return 0
        if prime in (i, j):
            return 1
        return 1 if (i - j) % prime in residues else -1

    c = [[entry(i, j) for j in points] for i in points]
    for i in points:
        for j in points:
            assert c[i][j] == c[j][i]
            assert sum(c[i][t] * c[j][t] for t in points) == prime * (i == j)
    return c


def verify_subset(c, plus):
    n = len(c)
    k = n // 2 - 1
    signs = [1 if i in plus else -1 for i in range(n)]
    complete = [row.copy() for row in c]
    for i, s in enumerate(signs):
        complete[i][i] = s
    gram = [[sum(x * y for x, y in zip(r, t)) for t in complete] for r in complete]
    blocks = []
    for s in (1, -1):
        points = [i for i, sign in enumerate(signs) if sign == s]
        block = [[gram[i][j] for j in points] for i in points]
        deviations = [gram[i][j] - n * (i == j) for i in points for j in points]
        assert sum(z * z for z in deviations) == 4 * k * (k + 1)
        assert all(gram[i][j] == n * (i == j) + 2 * s * c[i][j]
                   for i in points for j in points)
        assert all(gram[i][j] == 0 for i in points for j in range(n) if signs[j] != s)
        blocks.append(determinant(block))
    det = abs(determinant(complete))
    assert det * det == blocks[0] * blocks[1] and min(blocks) > 0
    assert det == blocks[0] == blocks[1]
    if n >= 16:
        bound = (2 * n - 2) * (n - 2) ** k
        ratio = Decimal(det) / Decimal(bound)
        error = abs(ratio.ln() - (Decimal('0.5') - Decimal(2).ln()))
        assert error < 4 * (Decimal(n - 1).sqrt() + 1) / n


def main():
    rng = Random(20261127)
    count = 0
    with localcontext() as context:
        context.prec = 65
        for prime in (5, 13, 17, 29, 37):
            c = paley(prime)
            n = len(c)
            if n == 6:
                selections = combinations(range(n), n // 2)
            else:
                selections = [rng.sample(range(n), n // 2) for _ in range(18)]
            for selection in selections:
                verify_subset(c, set(selection))
                count += 1
        for k in range(-1000, 3001):
            x = Decimal(k) / Decimal(13000)
            assert (1 + x).ln() >= x - Decimal(19) / 36 * x**2
    t = Fraction(17, 36)
    assert 1 + t + t**2 / 2 + t**3 / 6 > Fraction(8, 5)
    assert all((q + 1)**2 >= 676*q for q in range(674, 100000))
    assert (673 + 1)**2 < 676 * 673
    print(f'Checked {count} balanced completions of five Paley conference matrices.')
    print('Checked exact Gram blocks, second moments, determinants and the numerical log-rate tests.')


if __name__ == '__main__':
    main()
