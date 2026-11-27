"""Exact finite-order tests for split and nonsplit quadratic signings of Paley conference matrices.

The labels describe the signs on field coordinates. Correspondence to any
external author's family needs an independent structural identification.
Run with uv run --with python-flint python finite_check.py --output determinants.csv.
"""
import argparse
import csv
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from itertools import product
from math import isqrt
from pathlib import Path

from flint import fmpz_mat


def prime_power(q):
    for p in range(2, isqrt(q) + 1):
        if q % p == 0:
            n, exponent = q, 0
            while n % p == 0:
                n //= p
                exponent += 1
            return (p, exponent) if n == 1 else None
    return (q, 1) if q > 1 else None


def remainder(coefficients, monic, p):
    """Polynomial remainder in ascending coefficient order."""
    result = [a % p for a in coefficients]
    degree = len(monic) - 1
    for j in range(len(result) - 1, degree - 1, -1):
        leading = result[j]
        if leading:
            for i, coefficient in enumerate(monic):
                result[j-degree+i] = (result[j-degree+i] - leading*coefficient) % p
    return (result + [0]*degree)[:degree]


def irreducible(p, degree):
    divisors = [list(low) + [1] for k in range(1, degree//2 + 1)
                for low in product(range(p), repeat=k) if low[0] != 0]
    for low in product(range(p), repeat=degree):
        if low[0] == 0:
            continue
        monic = list(low) + [1]
        if all(any(remainder(monic, divisor, p)) for divisor in divisors):
            return monic
    raise ArithmeticError("No irreducible polynomial of the requested degree.")


def field_tables(q):
    p, degree = prime_power(q)
    if degree == 1:
        squares = [x*x % p for x in range(q)]
        subtraction = [[(x-y) % p for y in range(q)] for x in range(q)]
        return squares, subtraction
    modulus = irreducible(p, degree)
    weights = [p**j for j in range(degree)]
    digits = [[x//w % p for w in weights] for x in range(q)]

    def encode(a):
        return sum(w*c for w, c in zip(weights, a))

    def square(a):
        coeff = [0]*(2*degree - 1)
        for j, u in enumerate(a):
            for k, v in enumerate(a):
                coeff[j+k] += u*v
        return encode(remainder(coeff, modulus, p))

    subtraction = [[sum(w*((u-v) % p) for w, u, v in zip(weights, x, y))
                    for y in digits] for x in digits]
    return [square(x) for x in digits], subtraction


def conference_and_signs(q):
    squared, sub = field_tables(q)
    nonzero_squares = set(squared[1:])
    assert len(nonzero_squares) == (q-1)//2 and 0 not in nonzero_squares
    nonsquares = set(range(1, q)) - nonzero_squares
    chi = [0] + [1 if x in nonzero_squares else -1 for x in range(1, q)]
    c = [[chi[d] for d in row] + [1] for row in sub] + [[1]*q+[0]]
    # In the finite rows the off-diagonal Gram identities depend only on
    # the row difference. Translation preserves the sum over the field.
    assert all(c[x][y] == c[y][x] for x in range(q+1) for y in range(x))
    assert sum(chi) == 0 and sum(a*a for a in chi) == q-1
    assert all(sum(u*v for u, v in zip(c[0], c[j])) == 0 for j in range(1, q+1))
    d = min(nonsquares)
    signs = {
        'nonsplit-negative': {x for x in range(q) if chi[sub[squared[x]][d]] == -1},
        'split-squares': nonzero_squares | {0},
        'split-nonsquares': nonsquares | {0},
    }
    points = set(range(q+1))
    signs.update({name+'-opposite': points - subset for name, subset in list(signs.items())})
    assert all(len(s) == (q+1)//2 for s in signs.values())
    return c, signs


def gram_block_det(c, block, sign):
    n = len(c)
    ids = sorted(block)
    matrix = [[n if i == j else 2*sign*c[i][j] for j in ids] for i in ids]
    return int(fmpz_mat(matrix).det())


def check_order(q):
    c, signs = conference_and_signs(q)
    n = q+1
    bound = 2*q*(q-1)**((q-1)//2)
    rows = []
    for name, plus in signs.items():
        left = gram_block_det(c, plus, 1)
        right = gram_block_det(c, set(range(n))-plus, -1)
        assert left > 0 and right > 0
        square = left*right
        det = isqrt(square)
        assert det*det == square and left == right
        if n <= 50:
            direct = [[(1 if i in plus else -1) if i == j else c[i][j]
                       for j in range(n)] for i in range(n)]
            assert abs(int(fmpz_mat(direct).det())) == det
        assert 5*det >= 4*bound, (q, name, Fraction(det, bound))
        rows.append((q, name, det, bound))
    by_name = {name: value for _, name, value, _ in rows}
    assert by_name['split-squares-opposite'] == by_name['split-nonsquares']
    assert by_name['split-nonsquares-opposite'] == by_name['split-squares']
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--upper', type=int, default=673)
    args = parser.parse_args()
    if args.jobs < 1 or args.upper < 29:
        parser.error("Use a positive worker count and an upper limit of at least 29.")
    orders = [q for q in range(29, args.upper+1, 4) if prime_power(q)]
    if args.jobs == 1:
        rows = [r for q in orders for r in check_order(q)]
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as workers:
            rows = []
            for group in workers.map(check_order, orders):
                rows.extend(group)
                print(f"Checked q={group[0][0]}", flush=True)
    for name in dict.fromkeys(f for _, f, _, _ in rows):
        matching = [(Fraction(d,w),q) for q,f,d,w in rows if f == name]
        minimum,q = min(matching)
        print(f'{name}: min at q={q}, ratio {float(minimum):.12f}, q=29 ratio {matching[0][0]}')
    assert len(rows) == 6*len(orders)
    print(f'{len(orders)} prime powers; {len(rows)} exact determinants; minimum order {orders[0]+1}, maximum order {orders[-1]+1}.')
    if args.output:
        temporary = args.output.with_suffix(args.output.suffix + '.tmp')
        with temporary.open('w',newline='',encoding='ascii') as stream:
            writer = csv.writer(stream,lineterminator='\n')
            writer.writerow(['q','positive_coordinates','absolute_determinant','ehlich_wojtas_bound'])
            writer.writerows(rows)
        temporary.replace(args.output)


if __name__ == '__main__':
    main()
