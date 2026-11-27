"""Reproduce the cubic minor identities for the two-row rigidity test.

The five coefficients of a third row are variables. For the two prescribed
rows, every three-by-three minor of the complementary cubic block becomes
a cubic in those variables. Exact elimination writes a nonzero multiple
of each pure cube as a combination of minors after earlier variables vanish.
"""
import argparse
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations, product
from math import gcd, lcm, prod
from pathlib import Path

ROOT = Path(__file__).resolve().parent
COLS = range(5)
SECOND = (-3, -2, -1, 1, 2)
TRIPLES = tuple(combinations(COLS, 3))
PAIRS = tuple(combinations_with_replacement(TRIPLES, 2))
MONOMIALS = tuple(combinations_with_replacement(COLS, 3))


def weight(j, k, l):
    if len({j, k, l}) != 3:
        return 0
    a, b = sorted(set(COLS) - {j, k, l})
    return SECOND[a] + SECOND[b]


def minor_coefficients(rows, cols):
    coefficients = dict.fromkeys(MONOMIALS, 0)
    for p in permutations(range(3)):
        inversions = sum(p[a] > p[b] for a, b in combinations(range(3), 2))
        for indices in product(COLS, repeat=3):
            term = prod(weight(rows[a], cols[p[a]], indices[a]) for a in range(3))
            coefficients[tuple(sorted(indices))] += (-1) ** inversions * term
    return coefficients


def cube_relations(coefficients, active):
    monomials = [m for m in MONOMIALS if set(m) <= active]
    rows = [[minor[m] for m in monomials] for minor in coefficients]
    order = sorted(range(len(rows)), key=lambda i: (sum(bool(v) for v in rows[i]), max(map(abs, rows[i])), i))
    basis = {}
    for i in order:
        row = list(map(Fraction, rows[i]))
        comb = [Fraction(j == i) for j in range(len(rows))]
        for pivot, (b, c) in sorted(basis.items()):
            fact = row[pivot]
            if fact:
                row = [x - fact*y for x, y in zip(row, b)]
                comb = [x - fact*y for x, y in zip(comb, c)]
        pivot = next((p for p, val in enumerate(row) if val), None)
        if pivot is not None:
            fact = row[pivot]
            basis[pivot] = ([x/fact for x in row], [x/fact for x in comb])
    assert len(basis) == len(monomials)
    solutions = []
    for k in sorted(active):
        row = [Fraction(m == (k, k, k)) for m in monomials]
        comb = [Fraction(0)] * len(rows)
        for pivot, (b, c) in sorted(basis.items()):
            fact = row[pivot]
            if fact:
                row = [x - fact*y for x, y in zip(row, b)]
                comb = [x + fact*y for x, y in zip(comb, c)]
        assert not any(row)
        denominator = lcm(*(v.denominator for v in comb))
        terms = [(i, int(v*denominator)) for i, v in enumerate(comb) if v]
        assert gcd(denominator, *(abs(v) for _, v in terms)) == 1
        for m in monomials:
            assert sum(a*coefficients[i][m] for i, a in terms) == denominator * (m == (k, k, k))
        cost = (len(terms), max(abs(v) for _, v in terms).bit_length(), denominator, k)
        solutions.append((cost, k, denominator, terms))
    return min(solutions)[1:]


def vector(items):
    return "![" + ", ".join(map(str, items)) + "]"


def field_form(j, k):
    terms = [f"({weight(j,k,l)} : R) * v {l}" for l in COLS if weight(j,k,l)]
    return " + ".join(terms) or "0"


def write_source():
    coeffs = [minor_coefficients(r, c) for r, c in PAIRS]
    data = vector(vector(vector(weight(j,k,l) for l in COLS) for k in COLS) for j in COLS)
    matrix = vector(vector(field_form(j,k) for k in COLS) for j in COLS)
    text = """import PermanentLowerCubic

/-! Integral cubic certificates for the all-ones row and the row
(-3,-2,-1,1,2). If all three-dimensional minors of the lower Hessian block
vanish, every coordinate of the third row vanishes. -/
noncomputable section
open Matrix Finset
namespace PermanentFive

def twoRowPoint (u : Cell) : ℤ :=
  if u.1 = 0 then 1 else if u.1 = 1 then ![-3,-2,-1,1,2] u.2 else 0

"""
    text += "def twoRowCoeff (j k l : Idx) : ℤ :=\n  (" + data + ") j k l\n\n"
    text += "def twoRowBlock {R : Type*} [CommRing R] (v : Idx → R) : Matrix Idx Idx R :=\n  " + matrix + "\n\n"
    text += """set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
theorem twoRowCoeff_correct (j k l : Idx) : thirdWeight twoRowPoint j k l = twoRowCoeff j k l := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel

theorem twoRowBlock_sum {R : Type*} [CommRing R] (v : Idx → R) (j k : Idx) :
    twoRowBlock v j k = ∑ l, (twoRowCoeff j k l : R) * v l := by
  fin_cases j <;> fin_cases k <;> norm_num [twoRowBlock,twoRowCoeff,Fin.sum_univ_succ] <;> ring

set_option maxRecDepth 26000 in
set_option maxHeartbeats 10000000 in
theorem twoRowBlock_rigid {K : Type*} [Field K] [CharZero K] (v : Idx → K)
    (van : ∀ r c : Fin 3 → Idx, ((twoRowBlock v).submatrix r c).det = 0) : ∀ i, v i = 0 := by
"""
    active = set(COLS)
    known = []
    while active:
        k, denominator, terms = cube_relations(coeffs, active)
        rhs = []
        for index, a in terms:
            r, c = PAIRS[index]
            rhs.append(f"({a} : K) * ((twoRowBlock v).submatrix {vector(r)} {vector(c)}).det")
        text += f"  have z{k} : v {k} = 0 := by\n"
        text += f"    have id : ({denominator} : K) * (v {k})^3 =\n        " + " +\n        ".join(rhs) + " := by\n"
        simplify = ",".join(["Matrix.det_fin_three", "Matrix.submatrix", "twoRowBlock"] + [f"z{u}" for u in known])
        text += f"      norm_num [{simplify}]; ring\n"
        zeros = "van,mul_zero,add_zero" if len(terms) > 1 else "van,mul_zero"
        text += f"    simp only [{zeros}] at id\n"
        text += "    exact (pow_eq_zero_iff (by decide)).mp ((mul_eq_zero.mp id).resolve_left (by norm_num))\n"
        print(f"Coordinate {k}, terms {len(terms)}, multiplier {denominator}.")
        known.append(k)
        active.remove(k)
    text += "  intro i\n  fin_cases i\n" + "".join(f"  · exact z{k}\n" for k in COLS)
    text += "\n#print axioms twoRowCoeff_correct\n#print axioms twoRowBlock_rigid\nend PermanentFive\n"
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-lean", action="store_true")
    opts = parser.parse_args()
    source = write_source()
    target = ROOT / "PermanentTwoRowTemplate.lean"
    if opts.write_lean:
        target.write_text(source, encoding="utf8")
    else:
        assert target.read_text(encoding="utf8") == source
    print("Checked five pure-cube identities from the 55 symmetric minor choices.")


if __name__ == "__main__":
    main()
