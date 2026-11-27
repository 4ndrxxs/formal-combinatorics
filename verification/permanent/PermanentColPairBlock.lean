import PermanentPrincipal
import PermanentBlockShapes

/-! An exact integral Hessian block. The displayed right inverse after
clearing denominators is checked by multiplication in the Lean kernel. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 13 → Cell :=
  ![(0,1), (0,2), (0,3), (0,4), (1,1), (1,2), (1,3), (1,4), (2,0), (2,1), (2,2), (2,3), (2,4)]
private def centre (x : Cell) : ℤ :=
  if x ∈ ({(0,0), (2,0)} : Finset Cell) then 0 else 1
private def block : Matrix (Fin 13) (Fin 13) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 4, 4, 4, 6, 0, 6, 6, 6],
    ![0, 0, 0, 0, 4, 0, 4, 4, 6, 6, 0, 6, 6],
    ![0, 0, 0, 0, 4, 4, 0, 4, 6, 6, 6, 0, 6],
    ![0, 0, 0, 0, 4, 4, 4, 0, 6, 6, 6, 6, 0],
    ![0, 4, 4, 4, 0, 0, 0, 0, 6, 0, 4, 4, 4],
    ![4, 0, 4, 4, 0, 0, 0, 0, 6, 4, 0, 4, 4],
    ![4, 4, 0, 4, 0, 0, 0, 0, 6, 4, 4, 0, 4],
    ![4, 4, 4, 0, 0, 0, 0, 0, 6, 4, 4, 4, 0],
    ![6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 0],
    ![0, 6, 6, 6, 0, 4, 4, 4, 0, 0, 0, 0, 0],
    ![6, 0, 6, 6, 4, 0, 4, 4, 0, 0, 0, 0, 0],
    ![6, 6, 0, 6, 4, 4, 0, 4, 0, 0, 0, 0, 0],
    ![6, 6, 6, 0, 4, 4, 4, 0, 0, 0, 0, 0, 0]]
private def inverseNumerator : Matrix (Fin 13) (Fin 13) ℤ :=
  Matrix.of ![
    ![12, -4, -4, -4, -18, 6, 6, 6, -16, -4, 12, 12, 12],
    ![-4, 12, -4, -4, 6, -18, 6, 6, -16, 12, -4, 12, 12],
    ![-4, -4, 12, -4, 6, 6, -18, 6, -16, 12, 12, -4, 12],
    ![-4, -4, -4, 12, 6, 6, 6, -18, -16, 12, 12, 12, -4],
    ![-18, 6, 6, 6, 27, -9, -9, -9, 24, -26, -2, -2, -2],
    ![6, -18, 6, 6, -9, 27, -9, -9, 24, -2, -26, -2, -2],
    ![6, 6, -18, 6, -9, -9, 27, -9, 24, -2, -2, -26, -2],
    ![6, 6, 6, -18, -9, -9, -9, 27, 24, -2, -2, -2, -26],
    ![-16, -16, -16, -16, 24, 24, 24, 24, 192, -80, -80, -80, -80],
    ![-4, 12, 12, 12, -26, -2, -2, -2, -80, 44, 28, 28, 28],
    ![12, -4, 12, 12, -2, -26, -2, -2, -80, 28, 44, 28, 28],
    ![12, 12, -4, 12, -2, -2, -26, -2, -80, 28, 28, 44, 28],
    ![12, 12, 12, -4, -2, -2, -2, -26, -80, 28, 28, 28, 44]]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem entry_check : ∀ i j : Fin 13,
    secondAt centre (directions i) (directions j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem inverse_check : block * inverseNumerator = (192 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem nonsingular : block.det ≠ 0 :=
  det_ne_zero_of_inverse_certificate block inverseNumerator 192 (by decide) inverse_check

set_option maxRecDepth 20000 in
private theorem board_check : ∀ i ∈ colPairBoard, ∃ j, directions j = i := by decide +kernel

theorem col_pair_block (K : Type*) [Field K] [CharZero K] : HasThirteenBlock K colPairBoard :=
  block_of_integer colPairBoard directions board_check centre block entry_check nonsingular

#print axioms col_pair_block
end PermanentFive
