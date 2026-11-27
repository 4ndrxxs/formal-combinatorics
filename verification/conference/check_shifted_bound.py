"""Check the rational certificates for all even orders from 110 through 168."""
from fractions import Fraction
from math import isqrt


def parameters(v):
    q = 2*v-1
    a = Fraction(isqrt(q*10_000**2 // v**2)+1,10_000)
    squared = Fraction(1_000**2*(v-1)**2,v**2*q)
    nearest = isqrt(squared.numerator//squared.denominator)
    if 4*squared > (2*nearest+1)**2:
        nearest += 1
    return a,Fraction(nearest,1_000)


def certificate(v,a,b):
    z = (a+b)/(1+b)
    k = sum((z**j/(j+2) for j in range(7)),Fraction(0)) + z**7/(9*(1-z))
    p = sum(((-1)**(j+1)*b**j/j for j in range(1,7)),Fraction(0))
    def u(t):
        return t+t*t/2+t**3/3
    return (v*(p-b/(1+b)) - k*(1-Fraction(1,v)+v*b*b)/(1+b)**2
            + u(Fraction(1,2*v))+(v-1)*u(Fraction(1,v))-Fraction(470005,1_000_000))


def main():
    cases = []
    for v in range(55,85):
        a,b = parameters(v)
        assert 0 <= a < 1 and b >= 0 and 2*v-1 <= (v*a)**2
        value = certificate(v,a,b)
        assert value > Fraction(1,40000)
        cases.append((value,v))
    smallest,v = min(cases)
    print(f"Verified {len(cases)} rational moment certificates for every even order 110 through 168.")
    print(f"Smallest certified log margin {float(smallest):.12g} at order {2*v}, above 1/40000.")


if __name__ == '__main__':
    main()
