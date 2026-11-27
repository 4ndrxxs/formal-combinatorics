"""Evaluate the paired Jacobi product exactly and compare it with literal sign matrices."""
from check_lin_phoa import arrays
from check_projective import bareiss, eligible
from check_trace import Field


def product_on_nontrivial_roots(coefficients):
    """Norm of an integer polynomial modulo 1 + X + ... + X^(v-1)."""
    v = len(coefficients)
    size = v-1
    column = [x-coefficients[-1] for x in coefficients[:-1]]
    columns = []
    for _ in range(size):
        columns.append(column)
        top = column[-1]
        column = [-top] + [x-top for x in column[:-1]]
    return bareiss([list(row) for row in zip(*columns)])


def paired_coefficients(field):
    # At x = g^t, the characters psi and psi*eta contribute opposite
    # coefficients for odd t. An even exponent 2t contributes at X^t.
    v = (field.q-1)//2
    coefficients = [0]*v
    for exponent, x in enumerate(field.exp):
        pair = (1+field.char[x])*field.char[field.sub(1, x)]
        if exponent % 2:
            assert pair == 0
        else:
            coefficients[exponent//2] = pair
    assert sum(coefficients) == -2
    return coefficients


def main():
    count = 0
    for q in (q for q in eligible() if q < 169):
        field = Field(q)
        n, v = q+1, (q-1)//2
        pairs = paired_coefficients(field)
        products = {}
        for i in (0, 1):
            factors = [-((-1)**i)*x for x in pairs]
            factors[0] += n
            products[i] = product_on_nontrivial_roots(factors)
        for i, j, c, matrix in arrays(field):
            r = -1-(-1)**i
            constant_factor = 2*((c*r-v)**2+v*v)
            expected = (n-2)**2 if i else ((n*n+4) if c==1 else ((n-4)**2+4))
            assert constant_factor == expected
            det = constant_factor*products[i]
            assert det == abs(bareiss(matrix)), (q, i, j, c)
            count += 1
        print(f"q={q}: Jacobi products equal all eight literal determinants.", flush=True)
    print(f"Verified {count} exact determinant products over 18 fields.")


if __name__ == "__main__":
    main()
