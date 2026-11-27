"""Audit the determinant estimate for arbitrary diagonal signs on small Paley matrices."""

from decimal import Decimal, localcontext
from itertools import combinations
from random import Random

from check_conference import determinant, paley


def main():
    count = 0
    rng = Random(907)
    with localcontext() as context:
        context.prec = 65
        for prime in (5, 13, 17, 29, 37):
            c = paley(prime)
            n = prime + 1
            w = (2 * n - 2) * (n - 2) ** ((n - 2) // 2)
            for a in range(n + 1):
                sets = combinations(range(n), a) if n == 6 else [rng.sample(range(n), a)]
                for chosen in sets:
                    chosen = set(chosen)
                    m = [row.copy() for row in c]
                    for i in range(n):
                        m[i][i] = 1 if i in chosen else -1
                    gram = [[sum(x * y for x, y in zip(r, s)) for s in m] for r in m]
                    moment = sum((gram[i][j] - n * (i == j)) ** 2 for i in range(n) for j in range(n))
                    assert moment == 4 * (a * (a - 1) + (n - a) * (n - a - 1))
                    det = abs(determinant(m))
                    assert det > 0
                    if n >= 16:
                        ratio = Decimal(det) / w
                        alpha = Decimal(a) / n
                        expected = 2 * alpha * (1 - alpha) - Decimal(2).ln()
                        assert abs(ratio.ln() - expected) < (8 * Decimal(n - 1).sqrt() + 4) / n
                    if a in (0, n):
                        assert det == (n - 2) ** (n // 2)
                    count += 1
    print(f'Checked {count} diagonal assignments spanning every possible sign-class size in five orders.')


if __name__ == '__main__':
    main()
