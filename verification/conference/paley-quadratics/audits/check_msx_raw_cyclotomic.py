"""Check the original MSX character products directly at the eleven small Lean orders.

Run from this directory with
    uv run --no-project --with python-flint python check_msx_raw_cyclotomic.py

Integers in Z[zeta_L] are represented by polynomials modulo Phi_L. This
audit does not use the Gauss-to-Paley or Jacobi-to-Paley identities to
compute the source products.
"""
from math import lcm
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from flint import fmpz_poly

from check_msx_table import QuadraticExtension, values
from check_nonsplit_gauss import absolute_traces
from check_projective import eligible
from check_trace import Field


def as_integer(poly):
    assert poly.degree() <= 0, f"nonconstant result of degree {poly.degree()}"
    return int(poly[0])


def check_gauss(field):
    q = field.q
    n = q + 1
    v = n // 2
    order = lcm(4, v, field.p)
    phi = fmpz_poly.cyclotomic(order)
    trace = absolute_traces(field)
    base = [0] * order
    for x in range(1, q):
        base[trace[x] * (order // field.p)] += field.char[x]
    base_gauss = fmpz_poly(base) % phi
    ext = QuadraticExtension(field)
    trace_exponents = [
        trace[field.add(x, x)] * (order // field.p)
        for x, _ in ext.orbit(ext.generator, q*q - 1)
    ]
    products = [fmpz_poly([1]), fmpz_poly([1])]
    for j in range(v):
        sums = [[0] * order, [0] * order]
        for ell in (1, 3):
            step = ell * (order // 4) + j * (order // v)
            # With w = omega^v the phase is tau^(-ell)(w). Also check omega^(-1).
            phase = ell * v * (order // 4)
            for k, t in enumerate(trace_exponents):
                exponent = k * step + t
                sums[0][(exponent - phase) % order] += 1
                sums[1][(exponent + phase) % order] += 1
        for index, correction in enumerate(sums):
            numerator = (q*n - base_gauss * (fmpz_poly(correction) % phi)) % phi
            assert all(int(a) % q == 0 for a in numerator), (q, j, index)
            products[index] = (products[index] * (numerator // q)) % phi
    return [as_integer(x) for x in products]


def check_jacobi(field):
    q = field.q
    order = q - 1
    phi = fmpz_poly.cyclotomic(order)
    plus = fmpz_poly([(q-1)**2])
    minus = fmpz_poly([q*q + 2*q + 5])
    for j in range(1, (q-1)//2):
        first = [0] * order
        second = [0] * order
        for x in range(1, q):
            exponent = j * field.log[x] % order
            eta_one_minus_x = field.char[field.sub(1, x)]
            first[exponent] += field.char[x] * eta_one_minus_x
            second[exponent] += eta_one_minus_x
        pair = (fmpz_poly(first) + fmpz_poly(second)) % phi
        plus = (plus * (q+1 + pair)) % phi
        minus = (minus * (q+1 - pair)) % phi
    return [as_integer(plus), as_integer(minus)]


def main():
    orders = [q for q in eligible() if q < 109]
    assert len(orders) == 11
    for q in orders:
        field = Field(q)
        direct = check_gauss(field) + check_jacobi(field)
        assert direct == values(q, False), q
        w = 2*q*(q-1)**((q-1)//2)
        assert all(5*d >= 4*w for d in direct), q
        print(f"q={q}: four direct cyclotomic products equal the integer resultants; 5D >= 4W.", flush=True)
    print(f"All {4*len(orders)} direct character products passed exact arithmetic.")


if __name__ == "__main__":
    main()
