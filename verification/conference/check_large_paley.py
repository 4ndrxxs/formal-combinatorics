"""Recover an actual order-678 determinant exactly by modular Fourier evaluation and CRT."""

from decimal import Decimal, localcontext
from hashlib import sha256
from math import isqrt

from check_conference import determinant, paley


def distinct_factors(n):
    result = []
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            result.append(divisor)
            while n % divisor == 0:
                n //= divisor
        divisor += 1
    if n > 1:
        result.append(n)
    return result


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def root_of_order(k, prime):
    factors = distinct_factors(k)
    for candidate in range(2, prime):
        root = pow(candidate, (prime - 1) // k, prime)
        if all(pow(root, k // p, prime) != 1 for p in factors):
            return root
    raise ArithmeticError('The prime field does not contain the requested root.')


def recover_det(q):
    assert is_prime(q) and q % 4 == 1
    n = q + 1
    k = (q - 1) // 2
    squares = {z * z % q for z in range(1, q)}
    chi = [0] + [1 if z in squares else -1 for z in range(1, q)]
    assert all(sum(chi[z] * chi[(z + d) % q] for z in range(q)) == -1 for d in range(1, q))
    gen = root_of_order(k, q)
    field_points = [pow(gen, j, q) for j in range(k)]
    assert set(field_points) == squares
    # The positive coordinates are {0} together with the nonzero squares. On
    # the latter the Gram block is circulant. The negative block is obtained
    # by changing the sign of both border entries after nonsquare scaling.
    coefficients = [2 * chi[(z - 1) % q] for z in field_points]
    coefficients[0] += n
    assert all(coefficients[j] == coefficients[-j] for j in range(k))
    border = n * sum(coefficients) - 4 * k
    # Each Gram-block row has norm sqrt(n^2+4k) < n+1.
    absolute_bound = (n + 1) ** (k + 1)
    value = 0
    modulus = 1
    primes = 0
    candidate = ((2**26) // k) * k + 1
    while modulus <= 2 * absolute_bound:
        candidate += k
        if not is_prime(candidate):
            continue
        prime = candidate
        root = root_of_order(k, prime)
        residue = border % prime
        point = 1
        for j in range(1, k // 2 + 1):
            point = point * root % prime
            evaluation = 0
            for coefficient in reversed(coefficients):
                evaluation = (evaluation * point + coefficient) % prime
            residue = residue * evaluation % prime
            if j != k // 2:
                residue = residue * evaluation % prime
        correction = (residue - value) * pow(modulus, -1, prime) % prime
        value += correction * modulus
        modulus *= prime
        primes += 1
    if value > modulus // 2:
        value -= modulus
    assert 0 < value <= absolute_bound
    return value, primes


def main():
    for q in (5, 13, 29):
        c = paley(q)
        positive = {z * z % q for z in range(q)}
        for i in range(q + 1):
            c[i][i] = 1 if i in positive else -1
        assert recover_det(q)[0] == abs(determinant(c))
    q = 677
    n = q + 1
    value, primes = recover_det(q)
    bound = (2 * n - 2) * (n - 2) ** ((n - 2) // 2)
    assert 5 * value >= 4 * bound
    with localcontext() as context:
        context.prec = 30
        ratio = Decimal(value) / Decimal(bound)
    print(f'Order {n}, exact recovery from {primes} prime fields, |det|/W = {ratio}.')
    print('SHA-256 of the decimal determinant:', sha256(str(value).encode('ascii')).hexdigest())


if __name__ == '__main__':
    main()
