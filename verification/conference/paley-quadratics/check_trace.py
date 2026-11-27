"""Compute independent cubic-trace certificates for the small quadratic signings.

The finite fields use polynomial coordinates and multiplicative logarithms.
The determinant comparison uses only integer Bareiss elimination. Extension
fields may interchange the two nonsplit orientations when the chosen
nonsquare belongs to the other fourth-power class.
"""
import argparse
import json
from fractions import Fraction
from pathlib import Path

from check_projective import bareiss, eligible, table


# Monic moduli in ascending coefficient order; the complete cycle of a
# multiplicative generator certifies that the quotient is a field.
EXTENSIONS = {
    49: (7, (3,6,1)),
    81: (3, (2,0,0,2,1)),
    121: (11, (2,7,1)),
    125: (5, (3,3,0,1)),
    169: (13, (2,12,1)),
    289: (17, (3,16,1)),
    361: (19, (2,18,1)),
    529: (23, (5,21,1)),
    625: (5, (2,4,4,0,1)),
}


class Field:
    def __init__(self, q):
        self.q = q
        self.p, self.modulus = EXTENSIONS.get(q, (q, (0,1)))
        self.e = len(self.modulus)-1
        self.places = [self.p**i for i in range(self.e)]
        self.digits = [[(a//w) % self.p for w in self.places] for a in range(q)]
        assert self.p**self.e == q
        for g in range(2,q):
            powers, x = [1], g
            while x not in (0,1) and len(powers) < q:
                powers.append(x)
                x = self.multiply_polynomials(x,g)
            if x == 1 and len(powers) == q-1 and len(set(powers)) == q-1:
                self.exp = powers
                self.log = {v:j for j,v in enumerate(powers)}
                break
        else:
            raise ArithmeticError(f"No multiplicative generator for q={q}.")
        self.char = [0] + [1 if self.log[x] % 2 == 0 else -1 for x in range(1,q)]
        self.d = next(i for i,c in enumerate(self.char) if c == -1)

    def multiply_polynomials(self, x, y):
        p, n = self.p, self.e
        if n == 1:
            return x*y % p
        prod = [0]*(2*n-1)
        for i,a in enumerate(self.digits[x]):
            for j,b in enumerate(self.digits[y]):
                prod[i+j] += a*b
        for k in range(2*n-2,n-1,-1):
            for i in range(n):
                prod[k-n+i] -= prod[k]*self.modulus[i]
        return sum((c % p)*w for c,w in zip(prod,self.places))

    def add(self, x, y):
        if self.e == 1:
            return (x+y) % self.p
        return sum(((i+j) % self.p)*w for i,j,w in zip(self.digits[x],self.digits[y],self.places))

    def sub(self, x, y):
        if self.e == 1:
            return (x-y) % self.p
        return sum(((i-j) % self.p)*w for i,j,w in zip(self.digits[x],self.digits[y],self.places))

    def mul(self, x, y):
        return self.exp[(self.log[x]+self.log[y]) % (self.q-1)] if x and y else 0

    def inv(self, x):
        return self.exp[-self.log[x] % (self.q-1)]

    def signs(self):
        q = self.q
        positive = {i for i in range(1,q) if self.char[i] == 1}
        negative = set(range(1,q))-positive
        sets = {
            'split-squares':positive | {0},
            'split-nonsquares':negative | {0},
            'nonsplit-negative':{i for i in range(q) if self.char[self.sub(self.mul(i,i),self.d)] == -1},
        }
        sets.update({k+'-opposite':set(range(q+1))-v for k,v in list(sets.items())})
        return sets

    def matrix(self):
        q = self.q
        return [[self.char[self.sub(i,j)] for j in range(q)]+[1] for i in range(q)]+[[1]*q+[0]]


def verify(q, data):
    field = Field(q)
    c = field.matrix()
    n = q+1
    v = n//2
    assert all(sum(a*b for a,b in zip(c[0],c[j])) == q*(j == 0) for j in range(n))
    results = []
    for name, positive in field.signs().items():
        ids = sorted(positive)
        assert len(ids) == v
        block = [[c[i][j] for j in ids] for i in ids]
        words = [sum((t == -1) << j for j,t in enumerate(row)) for row in block]
        trace = 0
        for i in range(v):
            for j in range(i):
                hamming = (words[i]^words[j]).bit_count()
                trace += 2*(block[i][j]*(v-2*hamming)-2)
        direct = 6*sum(block[i][j]*block[j][k]*block[k][i] for i in range(v)
                       for j in range(i) for k in range(j))
        assert trace == direct
        margin = 87*v**3 + 375*v*(4*v-3) + 1000*trace - 1110*q*(v-1)
        assert margin >= 0, (q,name,margin)
        det = bareiss([[n if i == j else 2*block[i][j] for j in range(v)] for i in range(v)])
        if name.startswith('split'):
            assert det == data[q,name], (q,name)
        results.append(dict(signing=name, points=ids, negative_row_bits=[str(w) for w in words],
                            cubic_trace=trace, integer_margin=margin, determinant=str(det)))
    # Changing the model's nonsquare can exchange the two orientations.
    ns = ['nonsplit-negative','nonsplit-negative-opposite']
    assert sorted(int(r['determinant']) for r in results if r['signing'] in ns) == sorted(data[q,k] for k in ns)
    return dict(q=q, characteristic=field.p, polynomial=list(field.modulus), generator=field.exp[1],
                nonsquare=field.d, signs=results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    public_table = table()
    cases = [verify(q, public_table) for q in eligible() if q < 169]
    margins = [(Fraction(s['integer_margin'],3000*((case['q']+1)//2)**3),case['q'],s['signing'])
               for case in cases for s in case['signs']]
    lowest,q,which = min(margins)
    print(f"Verified {len(margins)} determinant and signed triangle computations over {len(cases)} fields.")
    print(f"Smallest rational certificate margin {lowest} at q={q}, {which}.")
    if args.output:
        outfile = args.output.with_suffix('.json.tmp')
        outfile.write_text(json.dumps(cases,indent=1)+'\n',encoding='ascii')
        outfile.replace(args.output)


if __name__ == '__main__':
    main()
