"""Reconstruct four signed coordinates and check every integer correlation."""
from hashlib import sha256

# Each code gives a sign and a coordinate. Multiplication by g**r fixes the
# first coordinate and rotates the other three.
SYSTEMS = (
    (271, 6, (1, 2, 5, 0, 7, 0, 4, 7, 4, 0, 4, 1, 5, 4, 4, 4, 0, 0)),
    (271, 6, (5, 4, 6, 7, 3, 1, 0, 6, 4, 6, 7, 3, 2, 2, 0, 4, 4, 0)),
    (271, 6, (1, 4, 2, 2, 1, 3, 0, 7, 4, 7, 5, 6, 7, 5, 0, 4, 4, 0)),
    (331, 3, (5, 4, 1, 0, 1, 5, 6, 0, 2, 0, 7, 1, 6, 4, 7, 3, 7, 0, 4, 2, 0, 4)),
)

def expand(p, g, codes):
    r = len(codes)
    assert (p-1) % (3*r) == 0 and all(0 <= a < 8 for a in codes)
    word = {0: 0}
    for exponent in range(p-1):
        x = pow(g, exponent, p)
        assert x not in word
        sign, axis = divmod(codes[exponent % r], 4)
        if axis:
            axis = 1 + (axis - 1 + exponent//r) % 3
        word[x] = 4*sign + axis
    return [word[x] for x in range(p)]

def correlations(rows, p):
    return [sum(row[x]*row[(x+s)%p] for row in rows for x in range(p))
            for s in range(p)]

def verify(p, g, codes):
    word = expand(p, g, codes)
    rows = [[(1 if a < 4 else -1) if a%4 == j else 0 for a in word]
            for j in range(4)]
    assert all(sum(row[x] != 0 for row in rows) == 1 for x in range(p))
    assert correlations(rows, p) == [p] + [0]*(p-1)
    skew = [rows[0][x] - sum(row[x] for row in rows[1:]) for x in range(p)]
    is_skew = skew[0] == 1 and all(skew[x] == -skew[-x] for x in range(1, p))
    print("period", p, "supports", [sum(x != 0 for x in row) for row in rows],
          "sums", list(map(sum, rows)), "skew projection", is_skew,
          "word sha256", sha256(bytes(word)).hexdigest())
    return is_skew

if __name__ == "__main__":
    results = [verify(*system) for system in SYSTEMS]
    assert results[2]

