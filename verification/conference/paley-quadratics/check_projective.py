"""Independent standard-library review of the finite table and projective sign orbits."""
import csv
from collections import deque
from fractions import Fraction
from itertools import product
from math import isqrt
from pathlib import Path


def bareiss(rows):
    a = [r.copy() for r in rows]
    previous, parity = 1, 1
    for j in range(len(a)-1):
        k = next((i for i in range(j,len(a)) if a[i][j]), None)
        if k is None:
            return 0
        if j != k:
            a[j], a[k] = a[k], a[j]
            parity = -parity
        pivot = a[j][j]
        for i in range(j+1,len(a)):
            for h in range(j+1,len(a)):
                numerator = pivot*a[i][h]-a[i][j]*a[j][h]
                a[i][h], remainder = divmod(numerator, previous)
                assert not remainder
        previous = pivot
    return parity*a[-1][-1]


def eligible():
    orders = set()
    for p in range(2, 674):
        if any(p % d == 0 for d in range(2,isqrt(p)+1)):
            continue
        q = p
        while q < 674:
            if q >= 29 and q % 4 == 1:
                orders.add(q)
            q *= p
    return sorted(orders)


def table():
    rows = {}
    with Path(__file__).with_name('determinants.csv').open(encoding='ascii') as src:
        for row in csv.DictReader(src):
            q = int(row['q'])
            name = row['positive_coordinates']
            det = int(row['absolute_determinant'])
            bound = int(row['ehlich_wojtas_bound'])
            assert (q,name) not in rows and det > 0
            assert bound == 2*q*pow(q-1,(q-1)//2) and 5*det >= 4*bound
            rows[q,name] = det
    names = {'nonsplit-negative','split-squares','split-nonsquares'}
    names |= {name+'-opposite' for name in names}
    assert set(rows) == set(product(eligible(),names))
    for q in eligible():
        assert rows[q,'split-squares'] == rows[q,'split-nonsquares-opposite']
        assert rows[q,'split-nonsquares'] == rows[q,'split-squares-opposite']
    print(f"All {len(rows)} entries account for {len(eligible())} eligible prime powers and give at least four fifths.")
    return rows


def projective_test(rows):
    p = 29
    n = p+1
    all_bits = (1 << n)-1
    pts = [(x,1) for x in range(p)] + [(1,0)]

    def chi(t):
        r = pow(t % p,(p-1)//2,p)
        return -1 if r == p-1 else r

    def idx(x,y):
        return x*pow(y,-1,p) % p if y % p else p

    c = [[chi(a*d-b*t) for t,d in pts] for a,b in pts]

    def det(mask):
        return abs(bareiss([[(1 if mask >> i & 1 else -1) if i == j else c[i][j]
                             for j in range(n)] for i in range(n)]))

    def mask(ids):
        return sum(1 << j for j in ids)

    nonsquare = next(x for x in range(1,p) if chi(x) < 0)
    seeds = {
        'nonsplit-negative':mask(x for x in range(p) if chi(x*x-nonsquare) < 0),
        'split-squares':mask(x for x in range(p) if x == 0 or chi(x) == 1),
        'split-nonsquares':mask(x for x in range(p) if x == 0 or chi(x) == -1),
    }
    seeds.update({name+'-opposite':m^all_bits for name,m in list(seeds.items())})
    generators = [(1,1,0,1),(nonsquare,0,0,1),(0,1,1,0)]
    actions = []
    for a,b,g,d in generators:
        factor = chi(a*d-b*g)
        image = [((a*x+b*y) % p,(g*x+d*y) % p) for x,y in pts]
        perm = [idx(x,y) for x,y in image]
        switch = [chi(y or x) for x,y in image]
        assert sorted(perm) == list(range(n))
        for i in range(n):
            for j in range(n):
                assert c[perm[i]][perm[j]] == factor*switch[i]*switch[j]*c[i][j]
        actions.append((factor,perm))

    values = {}
    queue = deque()
    for name,m in seeds.items():
        value = det(m)
        assert value == rows[p,name]
        values[m] = value
        queue.append(m)
    while queue:
        m = queue.popleft()
        for factor,perm in actions:
            image = mask(perm[i] for i in range(n) if m >> i & 1)
            if factor == -1:
                image ^= all_bits
            if image in values:
                assert values[image] == values[m]
            else:
                values[image] = values[m]
                queue.append(image)

    forms = [(1,b,d) for b,d in product(range(p), repeat=2)] + [(0,1,d) for d in range(p)]
    signed_masks = set()
    count = 0
    for a,b,d in forms:
        if (b*b-4*a*d) % p == 0:
            continue
        count += 1
        signs = [chi(a*x*x+b*x*y+d*y*y) for x,y in pts]
        assert sum(signs) == 0
        zeros = [i for i,s in enumerate(signs) if s == 0]
        assert len(zeros) in (0,2)
        pos = mask(i for i,s in enumerate(signs) if s == 1)
        choices = [pos] if not zeros else [pos | 1 << i for i in zeros]
        for m in choices:
            for oriented in (m, m^all_bits):
                assert oriented.bit_count() == n//2 and oriented in values
                signed_masks.add(oriented)
    assert count == p*p and signed_masks == set(values)
    for m in sorted(signed_masks)[::max(1,len(signed_masks)//20)]:
        assert det(m) == values[m]
    bound = 2*p*(p-1)**((p-1)//2)
    print(f"Order {n}: all {count} nonsingular binary quadratics up to scalar and {len(signed_masks)} distinct balanced signings occur in the signed projective orbits.")
    print("Four distinct exact determinant ratios:", sorted({str(Fraction(v,bound)) for v in values.values()}))


if __name__ == '__main__':
    projective_test(table())
