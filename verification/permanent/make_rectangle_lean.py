"""Generate the exact finite tables used in the Lean rectangle certificate."""
from fractions import Fraction
from itertools import product
from pathlib import Path

from check_quintic_discriminant import times
from check_quintic_rectangle import CELLS, matrices
from check_quintic_restricted import inverse_certificate

HERE = Path(__file__).resolve().parent
SIZE = 12


def lagrange(node, degree):
    coefficients = [Fraction(1)]
    denominator = 1
    for i in range(degree + 1):
        if i == node:
            continue
        coefficients = [a - i*b for a, b in zip([0] + coefficients, coefficients + [0])]
        denominator *= node - i
    return [a / denominator for a in coefficients]


def interpolate(table, degree):
    bases = [lagrange(i, degree) for i in range(degree + 1)]
    result = {}
    for u, v in product(range(degree+1), repeat=2):
        c = sum(bases[i][u] * bases[j][v] * z for (i,j), z in table.items())
        assert c.denominator == 1
        if c:
            result[u,v] = int(c)
    return result


def expression(poly):
    if not poly:
        return "0"
    parts = []
    for (i,j), c in sorted(poly.items()):
        factors = [a if d == 1 else f"{a}^{d}" for a,d in (('s',i),('t',j)) if d]
        if abs(c) != 1 or not factors:
            factors.insert(0,str(abs(c)))
        sign = ("-" if c < 0 else "") if not parts else (" - " if c < 0 else " + ")
        parts.append(sign + "*".join(factors))
    return "".join(parts)


def encode(rows, kind=""):
    prefix = f"{kind}.of " if kind else ""
    return prefix + "![" + ",\n     ".join("![" + ", ".join(row) + "]" for row in rows) + "]"


def write_matrix(name, table):
    expressions = [[expression(table[i,j]) for j in range(SIZE)] for i in range(SIZE)]
    return (f"def {name} {{R : Type*}} [CommRing R] (s t : R) : Mat R :=\n  "
            + encode(expressions,"Matrix") + "\n")


def change_tables():
    names = ("original","change","timesChange","split","inverseTwelve")
    samples = {k:{} for k in names}
    for s,t in product(range(3),repeat=2):
        h,p,g = matrices(s,t)
        _,denominator,inv = inverse_certificate(p)
        inverse = [[Fraction(12*v,denominator) for v in row] for row in inv]
        assert all(v.denominator == 1 for row in inverse for v in row)
        for k,mat in zip(names,(h,p,times(h,p),g,inverse)):
            samples[k][s,t] = mat
    return {k:{(i,j): interpolate({st:m[i][j] for st,m in sample.items()},2)
               for i,j in product(range(SIZE),repeat=2)} for k,sample in samples.items()}


def main():
    tables=change_tables()
    directions = "![" + ", ".join(f"({a//5},{a%5})" for a in CELLS) + "]"
    centre = [
        ["(1,1,0)","(-1,1,0)","(1,0,0)","(1,0,0)","(0,0,0)"],
        ["(1,0,1)","(1,0,0)","(-1,0,1)","(1,0,0)","(0,0,0)"],
        ["(1,0,0)","(1,0,0)","(1,0,0)","(3,0,0)","(0,0,0)"],
        ["(0,0,0)","(0,0,0)","(0,0,0)","(0,0,0)","(1,0,0)"],
        ["(1,0,0)","(1,0,0)","(1,0,0)","(-1,0,0)","(0,0,0)"]]
    src = ("import PermanentRectangleTokens\n\n"
        "/-! The entries of the three-by-four Hessian block at the two-parameter centre. -/\n\n"
        "open Matrix QuinticPencil\nnamespace PermanentFive.Rectangle\n"
        "abbrev Mat (R : Type*) := Matrix (Fin 12) (Fin 12) R\n"
        f"def directions : Fin 12 → Cell := {directions}\n"
        f"def centreCode (e : Cell) : Token :=\n  ({encode(centre)} : Idx → Idx → Token) e.1 e.2\n\n"
        + write_matrix("original",tables["original"]) + "\n")
    for slot, exp in zip(("constantCoeff","sCoeff","tCoeff"),((0,0),(1,0),(0,1))):
        rows=[[str(tables["original"][i,j].get(exp,0)) for j in range(SIZE)] for i in range(SIZE)]
        src+=f"private def {slot} : Mat ℤ :=\n  {encode(rows,'Matrix')}\n\n"
    src += """set_option maxRecDepth 32000 in
set_option maxHeartbeats 24000000 in
theorem rectangle_terms_affine (i j : Fin 12) : ∀ p, affineTag (termToken centreCode (directions i) (directions j) p) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 24000000 in
private theorem coeffs (i j : Fin 12) :
    blockCoefficient centreCode (directions i) (directions j) (0,0) = constantCoeff i j ∧
    blockCoefficient centreCode (directions i) (directions j) (1,0) = sCoeff i j ∧
    blockCoefficient centreCode (directions i) (directions j) (0,1) = tCoeff i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem hessian_original {R : Type*} [CommRing R] (s t : R) :
    (hessian (per R Idx) (value s t ∘ centreCode)).submatrix directions directions = original s t := by
  ext i j
  change hessian _ _ (directions i) (directions j) = _
  rw [second_formula,affine_second s t _ _ _ (rectangle_terms_affine i j)]
  obtain ⟨h₀,h₁,h₂⟩ := coeffs i j
  rw [h₀,h₁,h₂]
  fin_cases i <;> fin_cases j <;> norm_num [original,constantCoeff,sCoeff,tCoeff] <;> ring

#print axioms hessian_original
end PermanentFive.Rectangle
"""
    (HERE/"PermanentRectangleEntries.lean").write_text(src,encoding="utf8")
    tables_source=("import PermanentRectangleEntries\n\n/-! The integral Walsh and triangular changes of basis. -/\n\n"
                   "open Matrix\nnamespace PermanentFive.Rectangle\n")
    for name in ("change","timesChange","split","inverseTwelve"):
        tables_source+=write_matrix(name,tables[name])+"\n"
    tables_source+="end PermanentFive.Rectangle\n"
    (HERE/"PermanentRectangleMatrices.lean").write_text(tables_source,encoding="utf8")


if __name__ == "__main__":
    main()
