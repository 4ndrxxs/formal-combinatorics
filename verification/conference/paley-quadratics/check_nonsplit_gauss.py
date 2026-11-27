"""Check the nonsplit Gauss-sum differences in an integral group ring.

For an odd m=(q+1)/2 the output compares formal coefficients before any
root of unity is substituted. It therefore tests every character of the
torus, including characters of nonmaximal order and the trivial character.
"""

from check_projective import bareiss, eligible
from check_split_jacobi import product_on_nontrivial_roots
from check_trace import Field


def logarithm_table(field):
    """Powers of a primitive element of F[sqrt(d)], in polynomial coordinates."""
    q, d = field.q, field.d
    size = q*q - 1

    def multiply(z, w):
        x, y = z
        u, v = w
        return (field.add(field.mul(x, u), field.mul(d, field.mul(y, v))),
                field.add(field.mul(x, v), field.mul(y, u)))

    def power(z, n):
        result = (1, 0)
        while n:
            if n % 2:
                result = multiply(result, z)
            z = multiply(z, z)
            n //= 2
        return result

    primes = []
    remainder = size
    divisor = 2
    while divisor*divisor <= remainder:
        if remainder % divisor == 0:
            primes.append(divisor)
            while remainder % divisor == 0:
                remainder //= divisor
        divisor += 1
    if remainder > 1:
        primes.append(remainder)
    for y in range(1, q):
        for x in range(q):
            candidate = (x, y)
            if all(power(candidate, size//p) != (1, 0) for p in primes):
                powers = [(1, 0)]
                for _ in range(1, size):
                    powers.append(multiply(powers[-1], candidate))
                assert len(set(powers)) == size and multiply(powers[-1], candidate) == (1, 0)
                return powers
    raise ArithmeticError(f"No generator of the quadratic extension over q={q}.")


def absolute_traces(field):
    traces = []
    for x in range(field.q):
        total, conjugate = 0, x
        for _ in range(field.e):
            total = field.add(total, conjugate)
            if conjugate:
                conjugate = field.exp[field.p*field.log[conjugate] % (field.q-1)]
        assert conjugate == x and total < field.p
        traces.append(total)
    return traces


def verify(q):
    field = Field(q)
    p, m = field.p, (q+1)//2
    powers = logarithm_table(field)
    trace = absolute_traces(field)
    base_gauss = [0]*p
    for x in range(1, q):
        base_gauss[trace[x]] += field.char[x]

    torus = powers[::2*(q-1)]
    assert len(torus) == m and m % 2 == 1
    first = [field.char[y] for _, y in torus]
    second = [field.char[x] for x, _ in torus]
    assert first[0] == 0 and all(abs(a) == 1 for a in first[1:])
    assert all(abs(b) == 1 for b in second)
    # Divide the two sides by 2. Projection onto odd logarithms
    # is exactly (G(Omega)-G(Omega*eta_E))/2. Put U=2 sqrt(d).
    shift = powers.index((0, field.add(1, 1)))
    assert shift % 2 == 1
    coefficients = [[0]*p for _ in range(m)]
    half = pow(2, -1, m)
    for k in range(1, len(powers), 2):
        x, _ = powers[k]
        t = (k+shift)//2
        # Omega(g) = zeta_(4m)^a, where a is odd and a = -ell (mod m)
        # for theta(h)=zeta_m^ell. Thus Omega(U*g^k) =
        # (-1)^t * theta(h)^(-t/2); the exponent -t/2 is taken modulo m.
        mode = -t*half % m
        coefficients[mode][trace[field.add(x, x)]] += (-1)**t
    assert coefficients == [[a*b for b in base_gauss] for a in first], q

    for alpha in (-1, 1):
        factors = [2*alpha*t for t in first]
        factors[0] += q+1
        product = sum(factors)*product_on_nontrivial_roots(factors)
        filled = [alpha, *first[1:]]
        matrix = []
        for i in range(2*m):
            row = []
            for j in range(2*m):
                t = (j-i) % m
                if i//m == j//m:
                    row.append(filled[t] if i < m else -filled[t])
                else:
                    row.append(second[t])
            matrix.append(row)
        assert product == abs(bareiss(matrix)), (q, alpha)
    return m, m*p


def main():
    fields = [q for q in eligible() if q < 169]
    modes = coefficients = 0
    for q in fields:
        count, entries = verify(q)
        modes += count
        coefficients += entries
        print(f"q={q}: {count} characters and both full determinants agree.", flush=True)
    print(f"Verified {coefficients} integer coefficients for {modes} characters, "
          f"{2*len(fields)} full exact determinants, and {len(fields)} fields.")


if __name__ == "__main__":
    main()
