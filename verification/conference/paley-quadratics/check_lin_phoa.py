"""Construct Lin and Phoa's array (3.1) literally from the four 2022 cyclotomic sets."""
from fractions import Fraction
from itertools import product

from check_projective import bareiss, eligible
from check_split_borders import bits, gram_classes, sign_gram
from check_trace import Field


def arrays(field):
    squares = [field.exp[t] for t in range(0, field.q-1, 2)]
    nonsquares = set(range(1, field.q)) - set(squares)
    omega = field.exp[1]
    m = len(squares)
    for i, j in product((0, 1), repeat=2):
        first_coset = nonsquares if i else set(squares)
        second_coset = nonsquares if j else set(squares)
        first_set = {field.add(x, 1) for x in first_coset} & set(squares)
        second_set = {field.mul(omega, field.add(x, 1)) for x in second_coset} & set(squares)
        a = [1 if x in first_set else -1 for x in squares]
        b = [1 if x in second_set else -1 for x in squares]
        assert (sum(a), sum(b)) == (0 if i else -2, 0)
        for c in (1, -1):
            row0 = [c, c] + [1]*m + [1]*m
            row1 = [c, -c] + [1]*m + [-1]*m
            matrix = [row0, row1]
            for s in range(m):
                matrix.append([1, 1] + [a[(t-s) % m] for t in range(m)]
                              + [b[(t-s) % m] for t in range(m)])
            for s in range(m):
                matrix.append([1, -1] + [b[(s-t) % m] for t in range(m)]
                              + [-a[(s-t) % m] for t in range(m)])
            yield i, j, c, matrix


def main():
    checked = admitted = entries = 0
    for q in (q for q in eligible() if q < 169):
        f = Field(q)
        for i, j, c, matrix in arrays(f):
            n = q+1
            rows = [bits(row) for row in matrix]
            gram = sign_gram(rows, n)
            ok = gram_classes(gram) is not None
            assert ok == (i == 1 or c == 1), (q, i, j, c)
            checked += 1
            admitted += int(ok)
            entries += n*n
            if q == 29 and ok:
                ratio = Fraction(abs(bareiss(matrix)), 2*q*(q-1)**(q//2))
                assert ratio >= Fraction(4, 5)
                print(f"q={q}, i={i}, j={j}, c={c:+d}: |det|/W = {float(ratio):.12f}")
    print(f"Verified all {entries} Gram entries of {checked} literal arrays over 18 fields. "
          f"{admitted} satisfy the near-Hadamard partition.")


if __name__ == "__main__":
    main()
