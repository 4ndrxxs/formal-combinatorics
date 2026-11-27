"""Exact certificates for nine first-order discriminants and four ambient rank tests.

Run with Python 3.  The optional --write-lean flag emits the concrete Lean
modules, which independently evaluate all entries and matrix identities.
"""
import argparse
import json
from fractions import Fraction
from pathlib import Path

from check_quintic_endpoint import derivatives
from check_quintic_restricted import coordinate, inverse_certificate, lean_matrix, vector

ROOT = Path(__file__).resolve().parent
CELLS = tuple(range(25))
PURE = tuple(range(15))
MIXED = tuple(i for i in CELLS if i // 5 < 2 or i % 5 == 0)
PARENTS = [tuple(i for i in PURE if i not in holes) for holes in [(0, 1), (0, 5), (0, 6)]] + [MIXED]
JET_NAMES = ["PureA", "PureB", "PureC", "PureD", "PureE", "PureF", "MixedA", "MixedB", "MixedC"]
AMBIENT_NAMES = ["RowPair", "ColPair", "CrossPair", "Mixed"]


def times(a, b):
    return [[sum(x * y for x, y in zip(row, column)) for column in zip(*b)] for row in a]


def minor(a, rows, columns):
    return [[a[i][j] for j in columns] for i in rows]


def matrix_def(name, a):
    return f"private def {name} : Matrix (Fin {len(a)}) (Fin {len(a[0])}) ℤ :=\n  {lean_matrix(a)}\n"


def support_text(z):
    return "{" + ", ".join(coordinate(i) for i in z) + "}"


OPTIONS = "set_option maxRecDepth 26000 in\nset_option maxHeartbeats 24000000 in\n"


def jet_certificate(index, data, *, line_cover=False):
    if "cells" in data:
        cells = data["cells"]
        n, shape, shape_module = 10, "tenShape", "PermanentTenShapes"
        if line_cover:
            shape, shape_module = "lineTen", "PermanentLineBoards"
            name, thm = f"PermanentLineJet{index:02}", f"line_ten_odd_{index}"
        else:
            name, thm = "PermanentTenJet" + "ABCD"[index], "ten_odd_" + str(index)
        principal_det = data["principal_nine_determinant"]
    else:
        parent = PURE if data["cover"] == [3, 0] else MIXED
        cells = [i for i in parent if i not in data["holes"]]
        n, shape, shape_module = 12, "twelveShape", "PermanentTwelveShapes"
        name, thm = "PermanentJet" + JET_NAMES[index], "twelve_odd_" + str(index)
        principal_det = data["principal_eleven_determinant"]
    assert len(cells) == n
    last = n - 1
    z = [int(i not in data["simple_zero_centre_zeros"]) for i in CELLS]
    a = minor(derivatives(z)[1], cells, cells)
    direction = data["direction"]
    z[direction] += 1
    plus = minor(derivatives(z)[1], cells, cells)
    b = [[v - w for v, w in zip(row, base)] for row, base in zip(plus, a)]
    u = data["kernel"]
    assert all(sum(x*y for x, y in zip(row, u)) == 0 for row in a)
    keep = [i for i in range(n) if i != data["deleted_local_index"]]
    det, denominator, inv = inverse_certificate(minor(a, keep, keep))
    assert det == principal_det and u[data["deleted_local_index"]]
    v = [[int(i == j) for j in keep] + [u[i]] for i in range(n)]
    g = [row + [0] for row in inv] + [[0]*last + [1]]
    left = times(g, list(zip(*v)))
    la = times(left, a)
    diagonal = times(la, v)
    assert diagonal == [[denominator * (i == j and i != last) for j in range(n)] for i in range(n)]
    slope = times(times(left, b), v)[last][last]
    assert slope == data["kernel_derivative"] != 0
    s = f"""import PermanentIntegralJet
import {shape_module}

/-! Integer row and column operations certify the first-order determinant
on the {n} directions below. The last diagonal first derivative is {slope}. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin {n} → Cell :=
  {vector(map(coordinate, cells))}
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({support_text(data['simple_zero_centre_zeros'])} : Finset Cell) then 0 else 1,
   if x = {coordinate(direction)} then 1 else 0⟩
"""
    for key, matrix in [("constantPart", a), ("linearPart", b), ("leftChange", left),
                        ("rightChange", v), ("leftTimesConstant", la)]:
        s += matrix_def(key, matrix)
    conclusion = f"HasOddBlock K ({shape} {index})" if n == 12 else f"HasSimpleZeroBlock K {n} ({shape} {index})"
    constructor = "odd_block_of_integers" if n == 12 else f"simple_zero_of_integers {last}"
    s += f"""
{OPTIONS}private theorem entries : ∀ i j : Fin {n},
    secondAt centre (directions i) (directions j) =
      (⟨constantPart i j,linearPart i j⟩ : DualNumber ℤ) := by
  intro i j
  apply TrivSqZeroExt.ext <;> fin_cases i <;> fin_cases j <;> decide +kernel

{OPTIONS}private theorem left_check : leftChange * constantPart = leftTimesConstant := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

{OPTIONS}private theorem diagonal_check : ∀ i j : Fin {n},
    (leftChange * constantPart * rightChange) i j =
      if i=j ∧ i≠{last} then ({denominator} : ℤ) else 0 := by
  rw [left_check]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

{OPTIONS}private theorem slope_check : (leftChange * linearPart * rightChange) {last} {last} ≠ 0 := by decide +kernel

{OPTIONS}private theorem cover_check : ∀ j ∈ {shape} {index}, ∃ i, directions i = j := by decide +kernel

theorem {thm} (K : Type*) [Field K] [CharZero K] : {conclusion} :=
  {constructor} _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries {denominator} (by decide) diagonal_check slope_check

#print axioms {thm}
end PermanentFive
"""
    print(f"{name}: {last}-minor det {det}, denominator {denominator}, last diagonal slope {slope}")
    return name, s


def independent_minor(a, order):
    reduced = [list(map(Fraction, row)) for row in a]
    row_ids = list(range(len(a)))
    columns = []
    for col in range(len(a[0])):
        j = len(columns)
        pivot = next((i for i in range(j, len(a)) if reduced[i][col]), None)
        if pivot is None:
            continue
        reduced[j], reduced[pivot] = reduced[pivot], reduced[j]
        row_ids[j], row_ids[pivot] = row_ids[pivot], row_ids[j]
        for i in range(j+1, len(a)):
            q = reduced[i][col] / reduced[j][col]
            reduced[i] = [x-q*y for x, y in zip(reduced[i], reduced[j])]
        columns.append(col)
        if len(columns) == order:
            return row_ids[:order], columns
    raise ValueError("required ambient rank not attained")


def ambient_certificate(index, parent, *, line_cover=False):
    h = derivatives([int(i in parent) for i in CELLS])[1]
    rows, cols = independent_minor(h, 8)
    a = minor(h, rows, cols)
    det, denominator, inv = inverse_certificate(a)
    if line_cover:
        name, thm = f"PermanentLineAmbient{index:02}", f"line_ambient_{index}"
        shape, extra = "lineAmbient", "\nimport PermanentLineBoards"
    else:
        name, thm = "PermanentAmbient" + AMBIENT_NAMES[index], "thirteen_ambient_" + str(index)
        shape, extra = "thirteenShape", ""
    point = "the board indicator" if line_cover else "the indicator of a thirteen-cell board"
    s = f"""import PermanentAmbientEight{extra}

/-! An eight-by-eight nonsingular ambient minor at {point}. -/

namespace PermanentFive
open Matrix QuinticPencil
private def rows : Fin 8 → Cell := {vector(map(coordinate, rows))}
private def cols : Fin 8 → Cell := {vector(map(coordinate, cols))}
"""
    s += matrix_def("block", a) + matrix_def("inverseNumerator", inv)
    s += f"""
{OPTIONS}private theorem entries : ∀ i j : Fin 8,
    secondAt (boardPoint ({shape} {index})) (rows i) (cols j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

{OPTIONS}private theorem inverse_check : block * inverseNumerator = ({denominator} : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem {thm} (K : Type*) [Field K] [CharZero K] : HasAmbientEight K ({shape} {index}) :=
  ambient_eight_of_integers K _ rows cols block entries
    (det_ne_zero_of_inverse_certificate block inverseNumerator {denominator} (by decide) inverse_check)

#print axioms {thm}
end PermanentFive
"""
    print(f"{name}: rank-eight minor det {det}, denominator {denominator}")
    return name, s


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-lean", action="store_true")
    args = parser.parse_args()
    with (ROOT / "twelve-block-data.json").open(encoding="utf8") as stream:
        records = json.load(stream)
    certificates = [jet_certificate(i, d) for i, d in enumerate(records)]
    certificates.extend(ambient_certificate(i, p) for i, p in enumerate(PARENTS))
    assert len(certificates) == 13
    if args.write_lean:
        for name, src in certificates:
            (ROOT / (name + ".lean")).write_text(src, encoding="utf8")


if __name__ == "__main__":
    main()
