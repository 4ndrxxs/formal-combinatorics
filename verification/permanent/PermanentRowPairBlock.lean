import PermanentPrincipal
import PermanentBlockShapes

/-! An exact integral Hessian block. The displayed right inverse after
clearing denominators is checked by multiplication in the Lean kernel. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 13 → Cell :=
  ![(0,2), (0,3), (0,4), (1,0), (1,1), (1,2), (1,3), (1,4), (2,0), (2,1), (2,2), (2,3), (2,4)]
private def centre (_x : Cell) : ℤ :=
  1
private def block : Matrix (Fin 13) (Fin 13) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 6, 6, 0, 6, 6, 6, 6, 0, 6, 6],
    ![0, 0, 0, 6, 6, 6, 0, 6, 6, 6, 6, 0, 6],
    ![0, 0, 0, 6, 6, 6, 6, 0, 6, 6, 6, 6, 0],
    ![6, 6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 6],
    ![6, 6, 6, 0, 0, 0, 0, 0, 6, 0, 6, 6, 6],
    ![0, 6, 6, 0, 0, 0, 0, 0, 6, 6, 0, 6, 6],
    ![6, 0, 6, 0, 0, 0, 0, 0, 6, 6, 6, 0, 6],
    ![6, 6, 0, 0, 0, 0, 0, 0, 6, 6, 6, 6, 0],
    ![6, 6, 6, 0, 6, 6, 6, 6, 0, 0, 0, 0, 0],
    ![6, 6, 6, 6, 0, 6, 6, 6, 0, 0, 0, 0, 0],
    ![0, 6, 6, 6, 6, 0, 6, 6, 0, 0, 0, 0, 0],
    ![6, 0, 6, 6, 6, 6, 0, 6, 0, 0, 0, 0, 0],
    ![6, 6, 0, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0]]
private def inverseNumerator : Matrix (Fin 13) (Fin 13) ℤ :=
  Matrix.of ![
    ![1, -1, -1, 0, 0, -1, 1, 1, 0, 0, -1, 1, 1],
    ![-1, 1, -1, 0, 0, 1, -1, 1, 0, 0, 1, -1, 1],
    ![-1, -1, 1, 0, 0, 1, 1, -1, 0, 0, 1, 1, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, -3, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, -3, 1, 1, 1],
    ![-1, 1, 1, 0, 0, 1, -1, -1, 1, 1, -2, 0, 0],
    ![1, -1, 1, 0, 0, -1, 1, -1, 1, 1, 0, -2, 0],
    ![1, 1, -1, 0, 0, -1, -1, 1, 1, 1, 0, 0, -2],
    ![0, 0, 0, -3, 1, 1, 1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, -3, 1, 1, 1, 0, 0, 0, 0, 0],
    ![-1, 1, 1, 1, 1, -2, 0, 0, 0, 0, 1, -1, -1],
    ![1, -1, 1, 1, 1, 0, -2, 0, 0, 0, -1, 1, -1],
    ![1, 1, -1, 1, 1, 0, 0, -2, 0, 0, -1, -1, 1]]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem entry_check : ∀ i j : Fin 13,
    secondAt centre (directions i) (directions j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem inverse_check : block * inverseNumerator = (24 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem nonsingular : block.det ≠ 0 :=
  det_ne_zero_of_inverse_certificate block inverseNumerator 24 (by decide) inverse_check

set_option maxRecDepth 20000 in
private theorem board_check : ∀ i ∈ rowPairBoard, ∃ j, directions j = i := by decide +kernel

theorem row_pair_block (K : Type*) [Field K] [CharZero K] : HasThirteenBlock K rowPairBoard :=
  block_of_integer rowPairBoard directions board_check centre block entry_check nonsingular

#print axioms row_pair_block
end PermanentFive
