"""Coefficient sign tests for the determinant and permanent under variable partitions."""

from itertools import permutations, product


def inversions(values):
    return sum(x > y for i, x in enumerate(values) for y in values[i+1:]) % 2


def permutation_terms(n):
    return [(sum(1 << (n*i+j) for i,j in enumerate(perm)), inversions(perm))
            for perm in permutations(range(n))]


def bipartition_tests(n):
    """Test the shuffle and both local permutation signs for every subset of the edges."""
    terms = permutation_terms(n)
    phases = {}
    for full, _ in terms:
        matching = full
        while True:
            if matching not in phases:
                positions = [divmod(i, n) for i in range(n*n) if matching >> i & 1]
                local = inversions([j for _,j in positions])
                phases[matching] = ((local + sum(i+j for i,j in positions)) % 2, local)
            if not matching:
                break
            matching = (matching-1) & full
    for cut in range(1 << (n*n)):
        for full, parity in terms:
            left = full & cut
            right = full ^ left
            assert phases[left][0] ^ phases[right][1] == parity, (n, cut, full)
    return (1 << (n*n))*len(terms)


def in_binary_span(columns, target):
    pivots = {}
    for column in columns:
        while column:
            pivot = column.bit_length()-1
            if pivot not in pivots:
                pivots[pivot] = column
                break
            column ^= pivots[pivot]
    while target:
        pivot = target.bit_length()-1
        if pivot not in pivots:
            return False
        target ^= pivots[pivot]
    return True


def three_colour_tests():
    n = 3
    terms = permutation_terms(n)
    target = sum(parity << i for i, (_, parity) in enumerate(terms))
    obstructed = 0
    for colouring in product(range(3), repeat=n*n):
        masks = [sum(1 << i for i,c in enumerate(colouring) if c == k) for k in range(3)]
        labels = {}
        for i, (term, _) in enumerate(terms):
            for colour, mask in enumerate(masks):
                label = (colour, mask & term)
                labels[label] = labels.get(label, 0) | (1 << i)
        obstruction = not in_binary_span(labels.values(), target)
        all_rainbow = all((full & mask).bit_count() <= 1 for full, _ in terms for mask in masks)
        assert obstruction == all_rainbow
        row_colours = [set(colouring[n*i:n*i+n]) for i in range(n)]
        col_colours = [set(colouring[j::n]) for j in range(n)]
        stripes = any(all(len(c)==1 for c in groups) and len(set.union(*groups))==n
                      for groups in (row_colours, col_colours))
        assert obstruction == stripes
        obstructed += obstruction
    assert obstructed == 12
    return obstructed


if __name__ == "__main__":
    for n in range(1, 5):
        checked = bipartition_tests(n)
        print(f"n={n}: {checked} coefficient signs over all {2**(n*n)} two-colourings agree.")
    count = three_colour_tests()
    print(f"n=3: exactly {count} of 19683 three-colourings obstruct the local signs.")
