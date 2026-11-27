"""Reproduce five integral Hessian certificates for the order-five permanent.

Run without arguments to verify the data using exact rational arithmetic.
Pass --write-lean to regenerate the five concrete Lean certificate modules.
"""
import argparse
from fractions import Fraction
from math import lcm
from pathlib import Path

from check_quintic_endpoint import derivatives

ROOT = Path(__file__).resolve().parent
CELLS = tuple(range(25))
THREE_ROWS = tuple(range(15))
ONE_HOLE = tuple(i for i in THREE_ROWS if i != 0)
ALL_ONES = (1,) * 25


def indicator(cells):
    return tuple(int(i in cells) for i in CELLS)


def omit(cells, *holes):
    return tuple(i for i in cells if i not in holes)


# Each entry gives the module, its concrete theorem, the board, its ordered
# directions, and the integer matrix at which the Hessian is evaluated.
EXAMPLES = (
    ("PermanentRowPairBlock", "row_pair_block", "rowPairBoard",
     omit(THREE_ROWS, 0, 1), ALL_ONES),
    ("PermanentColPairBlock", "col_pair_block", "colPairBoard",
     omit(THREE_ROWS, 0, 5), indicator(omit(CELLS, 0, 10))),
    ("PermanentCrossPairBlock", "cross_pair_block", "crossPairBoard",
     omit(THREE_ROWS, 0, 6), ALL_ONES),
    ("PermanentMixedBlock", "mixed_block", "mixedBoard",
     tuple(i for i in CELLS if i // 5 < 2 or i % 5 == 0),
     indicator(omit(CELLS, 1, 4, 5, 10, 17, 18, 22, 24))),
    ("PermanentTenBlock", "row_hole_rank_ten", None,
     tuple(range(15, 25)), indicator(ONE_HOLE)),
)


def inverse_certificate(matrix):
    order = len(matrix)
    rows = [[Fraction(value) for value in row] +
            [Fraction(i == j) for j in range(order)] for i, row in enumerate(matrix)]
    det = Fraction(1)
    for j in range(order):
        pivot = next((i for i in range(j, order) if rows[i][j]), None)
        if pivot is None:
            raise ArithmeticError("singular Hessian block")
        if pivot != j:
            rows[j], rows[pivot] = rows[pivot], rows[j]
            det = -det
        scalar = rows[j][j]
        det *= scalar
        rows[j] = [a / scalar for a in rows[j]]
        for i in range(order):
            if i != j and rows[i][j]:
                factor = rows[i][j]
                rows[i] = [a - factor * b for a, b in zip(rows[i], rows[j])]
    inverse = [row[order:] for row in rows]
    divisor = lcm(*(a.denominator for row in inverse for a in row))
    integral = [[int(a * divisor) for a in row] for row in inverse]
    for i in range(order):
        for j in range(order):
            assert sum(matrix[i][k] * integral[k][j] for k in range(order)) == divisor * (i == j)
    assert det.denominator == 1
    return int(det), divisor, integral


def vector(entries):
    return "![" + ", ".join(map(str, entries)) + "]"


def lean_matrix(matrix):
    return "Matrix.of ![\n    " + ",\n    ".join(vector(row) for row in matrix) + "]"


def coordinate(cell):
    return f"({cell // 5},{cell % 5})"


def lean_module(theorem, board, indices, centre, entries, divisor, inverse):
    order = len(indices)
    board_import = "PermanentBlockShapes" if board else "PermanentMissingWitness"
    text = f"""import PermanentPrincipal
import {board_import}

/-! An exact integral Hessian block. The displayed right inverse after
clearing denominators is checked by multiplication in the Lean kernel. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin {order} → Cell :=
  {vector(map(coordinate, indices))}
"""
    point = "rowHole"
    if board:
        point = "centre"
        argument = "_x" if centre == ALL_ONES else "x"
        text += f"private def centre ({argument} : Cell) : ℤ :=\n  "
        if centre == ALL_ONES:
            text += "1\n"
        else:
            holes = [coordinate(i) for i, value in enumerate(centre) if not value]
            text += "if x ∈ ({" + ", ".join(holes) + "} : Finset Cell) then 0 else 1\n"
    text += f"""private def block : Matrix (Fin {order}) (Fin {order}) ℤ :=
  {lean_matrix(entries)}
private def inverseNumerator : Matrix (Fin {order}) (Fin {order}) ℤ :=
  {lean_matrix(inverse)}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem entry_check : ∀ i j : Fin {order},
    secondAt {point} (directions i) (directions j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem inverse_check : block * inverseNumerator = ({divisor} : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem nonsingular : block.det ≠ 0 :=
  det_ne_zero_of_inverse_certificate block inverseNumerator {divisor} (by decide) inverse_check
"""
    if board:
        text += f"""
set_option maxRecDepth 20000 in
private theorem board_check : ∀ i ∈ {board}, ∃ j, directions j = i := by decide +kernel

theorem {theorem} (K : Type*) [Field K] [CharZero K] : HasThirteenBlock K {board} :=
  block_of_integer {board} directions board_check centre block entry_check nonsingular
"""
    else:
        text += f"""
theorem {theorem} (K : Type*) [Field K] [CharZero K] :
    10 ≤ (hessian (per K Idx) ((Int.castRingHom K) ∘ rowHole)).rank :=
  integer_hessian_rank K _ directions directions block entry_check nonsingular
"""
    return text + f"\n#print axioms {theorem}\nend PermanentFive\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-lean", action="store_true")
    args = parser.parse_args()
    for module, theorem, board, indices, centre in EXAMPLES:
        _, hessian = derivatives(centre)
        block = [[hessian[i][j] for j in indices] for i in indices]
        det, divisor, inverse = inverse_certificate(block)
        print(f"{module}: rank {len(indices)}, determinant {det}, inverse denominator {divisor}")
        if args.write_lean:
            source = lean_module(theorem, board, indices, centre, block, divisor, inverse)
            (ROOT / f"{module}.lean").write_text(source, encoding="utf8")


if __name__ == "__main__":
    main()
