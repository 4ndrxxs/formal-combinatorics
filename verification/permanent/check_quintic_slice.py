"""Verify the five degree-six identities for the permanent slice over the integers."""

from collections import Counter
from itertools import permutations

ORDER = 5
INDICES = range(ORDER)

# Each term is (integer coefficient, missing row, missing column, first
# variable, second variable). Their sum is eight times the sixth power of
# the first coordinate. The other four identities are cyclic translates.
CERTIFICATE = (
    (8, 0, 0, 0, 0),
    (2, 0, 0, 2, 3),
    (-3, 0, 1, 0, 1),
    (-11, 0, 2, 0, 2),
    (-4, 0, 2, 1, 1),
    (-2, 0, 2, 3, 4),
    (1, 0, 3, 0, 3),
    (4, 0, 3, 1, 2),
    (-11, 0, 4, 0, 4),
    (-6, 0, 4, 1, 3),
    (6, 1, 0, 0, 4),
    (6, 1, 0, 2, 2),
    (-4, 1, 1, 0, 0),
    (-4, 1, 1, 1, 4),
    (-4, 1, 1, 2, 3),
    (4, 1, 2, 0, 1),
    (-2, 1, 2, 2, 4),
    (4, 1, 3, 0, 2),
    (-4, 1, 3, 3, 4),
    (6, 1, 4, 1, 2),
    (4, 1, 4, 4, 4),
    (6, 2, 0, 0, 3),
    (-10, 2, 0, 1, 2),
    (4, 2, 1, 1, 3),
    (-4, 2, 1, 2, 2),
    (2, 2, 2, 0, 0),
    (6, 2, 2, 1, 4),
    (4, 2, 2, 2, 3),
    (4, 2, 4, 0, 2),
    (2, 2, 4, 1, 1),
)


def complementary_permanent(row, col):
    """Expand the ambient first partial on the slice as a commutative polynomial."""
    rows = [i for i in INDICES if i != row]
    cols = [j for j in INDICES if j != col]
    result = Counter()
    for permuted_cols in permutations(cols):
        matching = list(zip(rows, permuted_cols))
        if any(j == 2 * i % ORDER for i, j in matching):
            continue
        monomial = tuple(sorted((j - i) % ORDER for i, j in matching))
        result[monomial] += 1
    return result


def translated_identity(shift, partials):
    result = Counter()
    for coefficient, row, col, a, b in CERTIFICATE:
        partial = partials[(row + shift) % ORDER, (col + 2 * shift) % ORDER]
        variables = ((a + shift) % ORDER, (b + shift) % ORDER)
        for monomial, multiplicity in partial.items():
            result[tuple(sorted(variables + monomial))] += coefficient * multiplicity
    return {word: n for word, n in result.items() if n}


def main():
    partials = {(r, c): complementary_permanent(r, c) for r in INDICES for c in INDICES}
    for shift in INDICES:
        actual = translated_identity(shift, partials)
        expected = {(shift,) * 6: 8}
        if actual != expected:
            raise AssertionError((shift, actual, expected))
    print("All five sixth-power identities hold over the integers for the 25 ambient partials.")


if __name__ == "__main__":
    main()
