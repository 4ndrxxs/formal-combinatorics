import PermanentIntegralJet
import PermanentTwelveShapes

/-! Integer row and column operations certify the first-order determinant
on the twelve directions below. The last diagonal first derivative is -8. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 12 → Cell :=
  ![(0,0), (0,1), (0,2), (0,3), (0,4), (1,0), (1,1), (1,2), (1,3), (1,4), (3,0), (4,0)]
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({(0,2), (0,4), (1,0), (1,1), (1,4), (2,0), (4,0), (4,3), (4,4)} : Finset Cell) then 0 else 1,
   if x = (4,0) then 1 else 0⟩
private def constantPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 2, 2, 4, 4, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 4],
    ![0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 1, 2],
    ![0, 0, 0, 0, 0, 4, 1, 1, 0, 2, 1, 2],
    ![0, 0, 0, 0, 0, 4, 1, 1, 2, 0, 3, 4],
    ![0, 2, 2, 4, 4, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 2],
    ![2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 4],
    ![4, 1, 1, 0, 2, 0, 0, 0, 0, 0, 1, 2],
    ![4, 1, 1, 2, 0, 0, 0, 0, 0, 0, 3, 4],
    ![0, 1, 1, 1, 3, 0, 1, 1, 1, 3, 0, 0],
    ![0, 4, 2, 2, 4, 0, 2, 4, 2, 4, 0, 0]]
private def linearPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def leftChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![3, 0, 0, 3, -3, 1, 8, -4, 5, -1, -6, 0],
    ![0, 0, 0, 0, 0, 4, -40, 8, 8, 8, 0, 0],
    ![3, 0, 0, 3, -3, 5, 10, -2, -5, 1, -6, 0],
    ![-3, 0, 0, -3, 3, -1, 10, -2, 1, -5, 6, 0],
    ![1, 0, 4, 5, -1, 3, 4, -4, 3, -3, -6, 0],
    ![8, 0, -40, 10, 10, 4, -20, 12, 2, 2, 12, -12],
    ![-4, 0, 8, -2, -2, -4, 12, -4, -2, -2, -12, 12],
    ![5, 0, 8, -5, 1, 3, 2, -2, 3, -3, -6, 0],
    ![-1, 0, 8, 1, -5, -3, 2, -2, -3, 3, 6, 0],
    ![-6, 0, 0, -6, 6, -6, 12, -12, -6, 6, 12, 0],
    ![0, 0, 0, 0, 0, 0, -12, 12, 0, 0, 0, 0],
    ![0, -1, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0]]
private def rightChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]
private def leftTimesConstant : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 24, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0],
    ![0, -24, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0],
    ![0, 24, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem entries : ∀ i j : Fin 12,
    secondAt centre (directions i) (directions j) =
      (⟨constantPart i j,linearPart i j⟩ : DualNumber ℤ) := by
  intro i j
  apply TrivSqZeroExt.ext <;> fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem left_check : leftChange * constantPart = leftTimesConstant := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem diagonal_check : ∀ i j : Fin 12,
    (leftChange * constantPart * rightChange) i j =
      if i=j ∧ i≠11 then (24 : ℤ) else 0 := by
  rw [left_check]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem slope_check : (leftChange * linearPart * rightChange) 11 11 ≠ 0 := by decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem cover_check : ∀ j ∈ twelveShape 8, ∃ i, directions i = j := by decide +kernel

theorem twelve_odd_8 (K : Type*) [Field K] [CharZero K] : HasOddBlock K (twelveShape 8) :=
  odd_block_of_integers _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries 24 (by decide) diagonal_check slope_check

#print axioms twelve_odd_8
end PermanentFive
