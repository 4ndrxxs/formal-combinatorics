import PermanentPrincipal
import PermanentMissingWitness

/-! An exact integral Hessian block. The displayed right inverse after
clearing denominators is checked by multiplication in the Lean kernel. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 10 → Cell :=
  ![(3,0), (3,1), (3,2), (3,3), (3,4), (4,0), (4,1), (4,2), (4,3), (4,4)]
private def block : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 6, 6, 6, 6],
    ![0, 0, 0, 0, 0, 6, 0, 4, 4, 4],
    ![0, 0, 0, 0, 0, 6, 4, 0, 4, 4],
    ![0, 0, 0, 0, 0, 6, 4, 4, 0, 4],
    ![0, 0, 0, 0, 0, 6, 4, 4, 4, 0],
    ![0, 6, 6, 6, 6, 0, 0, 0, 0, 0],
    ![6, 0, 4, 4, 4, 0, 0, 0, 0, 0],
    ![6, 4, 0, 4, 4, 0, 0, 0, 0, 0],
    ![6, 4, 4, 0, 4, 0, 0, 0, 0, 0],
    ![6, 4, 4, 4, 0, 0, 0, 0, 0, 0]]
private def inverseNumerator : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, -4, 2, 2, 2, 2],
    ![0, 0, 0, 0, 0, 2, -9, 3, 3, 3],
    ![0, 0, 0, 0, 0, 2, 3, -9, 3, 3],
    ![0, 0, 0, 0, 0, 2, 3, 3, -9, 3],
    ![0, 0, 0, 0, 0, 2, 3, 3, 3, -9],
    ![-4, 2, 2, 2, 2, 0, 0, 0, 0, 0],
    ![2, -9, 3, 3, 3, 0, 0, 0, 0, 0],
    ![2, 3, -9, 3, 3, 0, 0, 0, 0, 0],
    ![2, 3, 3, -9, 3, 0, 0, 0, 0, 0],
    ![2, 3, 3, 3, -9, 0, 0, 0, 0, 0]]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem entry_check : ∀ i j : Fin 10,
    secondAt rowHole (directions i) (directions j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem inverse_check : block * inverseNumerator = (48 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem nonsingular : block.det ≠ 0 :=
  det_ne_zero_of_inverse_certificate block inverseNumerator 48 (by decide) inverse_check

theorem row_hole_rank_ten (K : Type*) [Field K] [CharZero K] :
    10 ≤ (hessian (per K Idx) ((Int.castRingHom K) ∘ rowHole)).rank :=
  integer_hessian_rank K _ directions directions block entry_check nonsingular

#print axioms row_hole_rank_ten
end PermanentFive
