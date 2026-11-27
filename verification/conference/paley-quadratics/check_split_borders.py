"""Enumerate all constant sign borders of the two split Paley cores at selected small orders."""
import argparse
from itertools import product

from check_trace import Field


PAIRS = list(product((-1, 1), repeat=2))
SQUARES = list(product(PAIRS, repeat=2))


def bits(row):
    return sum(1 << i for i, value in enumerate(row) if value == -1)


def dot(x, y, n):
    return n - 2 * (x ^ y).bit_count()


def sign_gram(rows, n):
    return [[dot(a, b, n) for b in rows] for a in rows]


def gram_classes(gram):
    n = len(gram)
    masks = []
    for i, row in enumerate(gram):
        if row[i] != n or any(value not in (0, -2, 2) for j, value in enumerate(row) if i != j):
            return None
        group = sum(1 << j for j, value in enumerate(row) if value)
        if group.bit_count() != n // 2:
            return None
        masks.append(group)
    first = masks[0]
    other = ((1 << n) - 1) ^ first
    if any(mask != (first if first & (1 << i) else other) for i, mask in enumerate(masks)):
        return None
    return masks


def verify_cyclic_core(reference, m):
    first = reference[0][:m]
    mixed = reference[0][m:2*m]
    for i in range(m):
        for j in range(m):
            step = (j-i) % m
            assert reference[i][j] == first[step]
            assert reference[i][m+j] == mixed[step]
            assert reference[m+i][j] == mixed[-step % m]
            assert reference[m+i][m+j] == -first[step]

    def correlations(sequence):
        return [sum(x * sequence[(j+step) % m] for j, x in enumerate(sequence))
                for step in range(m)]

    for sequence in (first, mixed):
        original = correlations(sequence)
        for offset in range(m):
            for direction, scale in PAIRS:
                rotated = [scale * sequence[(offset+direction*j) % m] for j in range(m)]
                assert correlations(rotated) == original


def verify(q):
    field = Field(q)
    squares = field.exp[::2]
    nonsquares = [field.mul(field.exp[1], t) for t in squares]
    order = squares + nonsquares + [0, q]
    n, m = q + 1, len(squares)
    base = field.matrix()
    for alpha in (-1, 1):
        custom = [alpha]*m + [-alpha]*m + [1, -1]
        reference = [[base[u][v] if i != j else custom[i] for j, v in enumerate(order)]
                     for i, u in enumerate(order)]
        verify_cyclic_core(reference, m)
        fixed = sign_gram([bits(row) for row in reference], n)
        assert gram_classes(fixed)
        core = [bits(row[:-2]) for row in reference[:-2]]
        accepted = 0
        for top in SQUARES:
            top_rows = [row | (bits(top[i//m]) << (2*m)) for i, row in enumerate(core)]
            inside = sign_gram(top_rows, n)
            for left in SQUARES:
                low = [bits([a]*m + [b]*m) for a, b in left]
                for corner in SQUARES:
                    rim = [low[i] | (bits(corner[i]) << (2*m)) for i in (0, 1)]
                    columns = [[dot(row, last, n) for row in top_rows] for last in rim]
                    gram = [row + [columns[0][i], columns[1][i]] for i, row in enumerate(inside)]
                    cross = dot(*rim, n)
                    gram += [columns[0] + [n, cross], columns[1] + [cross, n]]
                    if gram_classes(gram) is None:
                        continue
                    accepted += 1
                    # Determine each boundary row's partner and sign from one row of its class.
                    changes = []
                    for j in range(2):
                        group = 0 if columns[j][0] else m
                        match = next(t for t in range(2) if fixed[group][2*m+t])
                        scale = columns[j][group] // fixed[group][2*m+match]
                        changes.append((2*m+match, scale))
                    perm = list(range(2*m)) + [k for k, _ in changes]
                    scales = [1]*(2*m) + [s for _, s in changes]
                    assert set(perm) == set(range(n)) and all(s in (-1, 1) for s in scales)
                    assert all(gram[i][j] == scales[i]*scales[j]*fixed[perm[i]][perm[j]]
                               for i in range(n) for j in range(n))
        assert accepted == (128 if alpha == -1 else 512)
        print(f"q={q}, square-class diagonal {alpha:+d}: {accepted} of 4096 borders satisfy the "
              "two-class Gram condition; each full Gram matrix agrees after border permutation and signs.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", type=int, choices=(5, 29, 37, 41, 49, 53, 61, 73, 81, 89, 97, 101), default=29)
    verify(parser.parse_args().q)
