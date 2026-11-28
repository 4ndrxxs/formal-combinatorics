"""Recompute the three determinant products in MSX Theorem 1.6, rows 4–6.

Run from this directory with
    uv run --no-project --with python-flint python check_msx_table.py

The finite part of the short proof covers every eligible q below 674.
All products and inequalities use exact integers.  The optional --raw flag
also compares every character sum at q=29 to its finite Fourier reduction
using complex arithmetic as an independent check of the phase convention.
"""

import argparse
import cmath
from fractions import Fraction
from math import pi

from flint import fmpz_poly

from check_nonsplit_gauss import absolute_traces
from check_projective import eligible, table
from check_split_jacobi import paired_coefficients
from check_trace import Field


def prime_divisors(n):
    factors = []
    i = 2
    while i * i <= n:
        if n % i == 0:
            factors.append(i)
            while n % i == 0:
                n //= i
        i += 1
    if n > 1:
        factors.append(n)
    return factors


class QuadraticExtension:
    def __init__(self, field):
        self.field = field
        self.size = field.q**2 - 1
        factors = prime_divisors(self.size)
        self.generator = next(
            (x, y) for y in range(1, field.q) for x in range(field.q)
            if all(self.power((x, y), self.size // p) != (1, 0) for p in factors)
        )
        assert self.power(self.generator, self.size) == (1, 0)

    def multiply(self, z, u):
        f = self.field
        x, y = z
        a, b = u
        return (f.add(f.mul(x, a), f.mul(f.d, f.mul(y, b))),
                f.add(f.mul(x, b), f.mul(y, a)))

    def power(self, z, exponent):
        result = (1, 0)
        while exponent:
            if exponent % 2:
                result = self.multiply(result, z)
            z = self.multiply(z, z)
            exponent //= 2
        return result

    def orbit(self, z, size):
        t = (1, 0)
        for _ in range(size):
            yield t
            t = self.multiply(t, z)
        assert t == (1, 0)


def determinant_product(coefficients, include_trivial):
    """Resultant of the cyclotomic product (monic) and the eigenvalue polynomial."""
    size = len(coefficients)
    roots = [-1] + [0] * (size-1) + [1] if include_trivial else [1] * size
    return int(fmpz_poly(roots).resultant(fmpz_poly(coefficients)))


def raw_check(field, extension, first, orient):
    q = field.q
    n, v, m = q+1, (q+1)//2, (q-1)//2
    base_trace = absolute_traces(field)
    zeta = lambda k: cmath.exp(2j * pi / k)
    add = [zeta(field.p)**t for t in base_trace]
    G = sum(field.char[x] * add[x] for x in range(1,q))
    powers = list(extension.orbit(extension.generator, extension.size))
    addK = [add[field.add(x,x)] for x, _ in powers]
    z = zeta(v)
    for j in range(v):
        value = 0j
        for ell in (1,3):
            gauss = sum((1j)**((ell*k)%4) * z**((j*k)%v) * a for k,a in enumerate(addK))
            value += (1j)**((-ell*v)%4) * gauss
        symbol = sum(z**((j*2*(q-1)*k)%v) * a for k,a in enumerate(first))
        assert abs((n-G*value/q) - (n+2*orient*symbol)) < 1e-7, ('Gauss',q,j)
    for j in range(1,m):
        zbase = zeta(q-1)
        jsum = sum((1+field.char[x]) * zbase**((field.log[x]*j)%(q-1))
                   * field.char[field.sub(1,x)] for x in range(1,q))
        sq = sum(zeta(m)**((j*t)%m) * a for t,a in enumerate(paired_coefficients(field)))
        assert abs(jsum-sq) < 1e-7, ('Jacobi',q,j)


def values(q, raw):
    n, v = q+1, (q+1)//2
    field = Field(q)
    extension = QuadraticExtension(field)
    h = extension.power(extension.generator, 2*(q-1))
    first = [field.char[y] for _,y in extension.orbit(h, v)]
    assert first[0] == 0 and all(abs(a) == 1 for a in first[1:])
    x, t = extension.power(extension.generator, v)
    assert x == 0 and t != 0
    orient = field.char[field.mul(field.add(1,1), field.inv(t))]
    if raw:
        raw_check(field, extension, first, orient)
    determinants = []
    for a in (orient, -orient):
        coeff = [2*a*b for b in first]
        coeff[0] += n
        determinants.append(determinant_product(coeff, True))
    jac = paired_coefficients(field)
    for sign, prefactor in ((1,(q-1)**2), (-1,n*n+4)):
        coeff = [sign * x for x in jac]
        coeff[0] += n
        determinants.append(prefactor * determinant_product(coeff, False))
    return determinants


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--raw', action='store_true')
    opts = parser.parse_args()
    old = table()
    least = None
    for q in eligible():
        bound = 2*q*(q-1)**((q-1)//2)
        d4, d4rev, d5, d6 = values(q, opts.raw and q == 29)
        assert sorted((d4,d4rev)) == sorted((old[q,'nonsplit-negative'],old[q,'nonsplit-negative-opposite']))
        assert d5 == old[q,'split-squares'] and d6 == old[q,'split-nonsquares']
        for name, det in [('4',d4),('4 (reversed orientation)',d4rev),('5',d5),('6',d6)]:
            assert 5*det >= 4*bound, (q,name)
            current = (Fraction(det,bound),q,name)
            least = current if least is None else min(least,current)
        if q == 29:
            print('q=29, class 4 for this generator, its reverse, class 5, class 6:')
            print(' '.join(f'{x/bound:.12f}' for x in (d4,d4rev,d5,d6)))
    print(f'{len(eligible())} fields checked exactly; minimum across all four products '
          f'{float(least[0]):.12f} at q={least[1]}, class {least[2]}.')
    if opts.raw:
        print('Individual raw complex Gauss and Jacobi factors agreed at q=29.')


if __name__ == '__main__':
    main()
