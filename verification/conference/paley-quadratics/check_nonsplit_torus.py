"""Compare the two circulants from a norm-one group with the nonsplit Paley matrix."""
from fractions import Fraction

from check_projective import bareiss, eligible
from check_trace import Field


def verify(q):
    f = Field(q)
    d = f.d
    v = (q+1)//2
    assert v % 2 == 1 and f.char[f.sub(0, 1)] == 1

    # Represent a + b sqrt(d) by (a,b). Its norm is a^2 - d*b^2.
    def multiply(u, w):
        a, b = u
        x, y = w
        return (f.add(f.mul(a, x), f.mul(d, f.mul(b, y))),
                f.add(f.mul(a, y), f.mul(b, x)))

    def norm(u):
        return f.sub(f.mul(u[0], u[0]), f.mul(d, f.mul(u[1], u[1])))

    group = None
    for t in range(q):
        # The square of (t + sqrt(d))/(t - sqrt(d)) has order dividing v.
        inverse_norm = f.inv(norm((t, 1)))
        u = tuple(f.mul(a, inverse_norm) for a in multiply((t, 1), (t, 1)))
        h = multiply(u, u)
        potential, seen, term = [], set(), (1, 0)
        while term not in seen and len(potential) <= v:
            potential.append(term)
            seen.add(term)
            term = multiply(term, h)
        if len(potential) == v and term == (1, 0):
            group = potential
            break
    assert group is not None and all(norm(u) == 1 for u in group)
    vectors = group + [multiply((0, 1), u) for u in group]
    assert all(f.char[norm(z)] == (1 if k < v else -1) for k, z in enumerate(vectors))
    # (a,b) is b*(a/b,1) or a*(1,0); the latter index is q.
    projective = [f.mul(a, f.inv(b)) if b else q for a, b in vectors]
    switch = [f.char[b or a] for a, b in vectors]
    assert sorted(projective) == list(range(q+1)) and all(abs(s) == 1 for s in switch)
    paley = f.matrix()

    ratios = []
    first, second = [f.char[b] for a, b in group], [f.char[a] for a, b in group]
    assert first[0] == 0 and all(abs(a) == 1 for a in first[1:])
    assert all(abs(b) == 1 for b in second)
    assert all(first[k] == first[-k % v] and second[k] == second[-k % v] for k in range(v))
    for alpha in (-1, 1):
        a = [alpha, *first[1:]]
        def value(i, j):
            step = (j-i) % v
            if i//v == j//v:
                return a[step] if i < v else -a[step]
            return second[step]

        for i in range(q+1):
            for j in range(q+1):
                ref = alpha*f.char[norm(vectors[i])] if i == j else paley[projective[i]][projective[j]]
                assert value(i, j) == switch[i]*switch[j]*ref, (q, alpha, i, j)
        for k in range(1, v):
            corr = sum(a[t]*a[(t+k) % v] + second[t]*second[(t+k) % v] for t in range(v))
            assert corr == 2*alpha*first[k], (q, alpha, k)
        if q == 29:
            det = abs(bareiss([[value(i,j) for j in range(q+1)] for i in range(q+1)]))
            ratios.append(Fraction(det, 2*q*(q-1)**(q//2)))
    return 2*(q+1)**2, ratios


def main():
    fields = [q for q in eligible() if q < 169]
    checked = 0
    for q in fields:
        entries, ratios = verify(q)
        checked += entries
        if ratios:
            print(f"Order {q+1} determinant ratios for the two orientations: "
                  + ", ".join(f"{float(r):.12f}" for r in ratios))
    print(f"Verified {checked} signed projective matrix entries and every cyclic correlation "
          f"at {len(fields)} fields from {min(fields)} through {max(fields)}.")


if __name__ == "__main__":
    main()
