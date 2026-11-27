import PermanentPrincipal
import PermanentBlockShapes

/-! An exact integral Hessian block. The displayed right inverse after
clearing denominators is checked by multiplication in the Lean kernel. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 13 → Cell :=
  ![(0,0), (0,1), (0,2), (0,3), (0,4), (1,0), (1,1), (1,2), (1,3), (1,4), (2,0), (3,0), (4,0)]
private def centre (x : Cell) : ℤ :=
  if x ∈ ({(0,1), (0,4), (1,0), (2,0), (3,2), (3,3), (4,2), (4,4)} : Finset Cell) then 0 else 1
private def block : Matrix (Fin 13) (Fin 13) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 1, 3, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 2, 1, 1, 1, 2, 2],
    ![0, 0, 0, 0, 0, 3, 2, 0, 3, 3, 3, 4, 4],
    ![0, 0, 0, 0, 0, 1, 1, 3, 0, 2, 1, 2, 4],
    ![0, 0, 0, 0, 0, 1, 1, 3, 2, 0, 1, 4, 2],
    ![0, 1, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 2, 1, 1, 0, 0, 0, 0, 0, 1, 1, 2],
    ![3, 2, 0, 3, 3, 0, 0, 0, 0, 0, 1, 1, 2],
    ![1, 1, 3, 0, 2, 0, 0, 0, 0, 0, 1, 1, 2],
    ![1, 1, 3, 2, 0, 0, 0, 0, 0, 0, 1, 3, 2],
    ![0, 1, 3, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0],
    ![0, 2, 4, 2, 4, 0, 1, 1, 1, 3, 0, 0, 0],
    ![0, 2, 4, 4, 2, 0, 2, 2, 2, 2, 0, 0, 0]]
private def inverseNumerator : Matrix (Fin 13) (Fin 13) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 2, 2, -4, 0, 8, 0, -4],
    ![0, 1, 0, 0, -1, -1, -5, 0, 4, 1, -2, -1, 2],
    ![0, 0, 0, 0, 0, 1, 1, 0, -1, 0, 2, 0, -1],
    ![0, 0, 0, 0, 0, 1, 1, 0, -1, 0, -2, 0, 1],
    ![0, -1, 0, 0, 1, 1, 1, 0, 0, -1, -2, 1, 0],
    ![0, -1, 1, 1, 1, 8, 2, 2, -6, -2, 4, 0, -4],
    ![2, -5, 1, 1, 1, 2, 0, 0, 0, 0, -2, 0, 0],
    ![2, 0, 0, 0, 0, 2, 0, 0, 0, 0, -2, 0, 0],
    ![-4, 4, -1, -1, 0, -6, 0, 0, 1, -1, 6, -1, 1],
    ![0, 1, 0, 0, -1, -2, 0, 0, -1, 1, 2, 1, -1],
    ![8, -2, 2, -2, -2, 4, -2, -2, 6, 2, -16, 0, 4],
    ![0, -1, 0, 0, 1, 0, 0, 0, -1, 1, 0, 1, -1],
    ![-4, 2, -1, 1, 0, -4, 0, 0, 1, -1, 4, -1, 1]]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem entry_check : ∀ i j : Fin 13,
    secondAt centre (directions i) (directions j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem inverse_check : block * inverseNumerator = (4 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem nonsingular : block.det ≠ 0 :=
  det_ne_zero_of_inverse_certificate block inverseNumerator 4 (by decide) inverse_check

set_option maxRecDepth 20000 in
private theorem board_check : ∀ i ∈ mixedBoard, ∃ j, directions j = i := by decide +kernel

theorem mixed_block (K : Type*) [Field K] [CharZero K] : HasThirteenBlock K mixedBoard :=
  block_of_integer mixedBoard directions board_check centre block entry_check nonsingular

#print axioms mixed_block
end PermanentFive
