"""Verify the two-variable Hessian-congruence certificate by exact integer interpolation."""
from itertools import product

from check_quintic_discriminant import minor, times
from check_quintic_endpoint import derivatives
from check_quintic_restricted import inverse_certificate

CELLS = tuple(5*i+j for i in range(3) for j in range(4))
WALSH = ((1, 1, 1, 1), (1, 1, -1, -1), (1, -1, 1, -1), (1, -1, -1, 1))


def matrices(s, t):
    centre = [s, -s, 1, 1, 0, t, 1, -t, 1, 0, 1, 1, 1, 3, 0,
              0, 0, 0, 0, 1, 1, 1, 1, -1, 0]
    hessian = minor(derivatives(centre)[1], CELLS, CELLS)
    a, b, c = (1, -1, s, -s), (1, t, -1, -t), (3, -1, -1, -1)
    change = [[0]*12 for _ in range(12)]
    expected = [[0]*12 for _ in range(12)]
    for i, j in product(range(4), repeat=2):
        w = WALSH[i][j]
        change[i][j] = change[4+i][4+j] = w
        change[i][8+j] = -w*a[j]
        change[4+i][8+j] = -w*b[j]
        change[8+i][8+j] = w*c[j]
    for j in range(4):
        expected[j][4+j] = expected[4+j][j] = 8*c[j]
        expected[8+j][8+j] = (-48, -16*t, -16*s, 16*s*t)[j]
    return hessian, change, expected


def main():
    # Each differentiated permutation term uses at most one entry from
    # each row. Only row 0 contains s and only row 1 contains t.
    # Hence H has separate degrees at most (1,1). Each change factor is
    # affine, giving separate degrees at most (3,3) for the congruence.
    for s, t in product(range(4), repeat=2):
        h, p, expected = matrices(s, t)
        assert times(times(list(zip(*p)), h), p) == expected
        centre = [s, -s, 1, 1, 0, t, 1, -t, 1, 0, 1, 1, 1, 3, 0,
                  0, 0, 0, 1, 1, 1, 1, 1, -1, 0]
        large = minor(derivatives(centre)[1],range(15),range(15))
        fold = [4*(i//5)+min(i%5,3) for i in range(15)]
        assert large == minor(h,fold,fold)
    # P is block upper triangular. Its determinant is independent of both
    # variables and equals det(W)^3 times the product of the c coefficients.
    wdet = inverse_certificate(WALSH)[0]
    d = wdet**3 * (3*(-1)**3)
    assert abs(d) == 12288
    assert inverse_certificate(matrices(0, 0)[1])[0] == d
    print(f"All 144 polynomial identities hold on a degree-determining 4 by 4 grid. "
          f"The integral change of basis has constant determinant {d}.")
    print("Four hyperbolic planes and diagonal remainder (-48,-16t,-16s,16st).")


if __name__ == "__main__":
    main()
