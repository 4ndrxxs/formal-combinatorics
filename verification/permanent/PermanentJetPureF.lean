import PermanentIntegralJet
import PermanentTwelveShapes

/-! Integer row and column operations certify the first-order determinant
on the twelve directions below. The last diagonal first derivative is 4. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 12 → Cell :=
  ![(0,1), (0,2), (0,3), (0,4), (1,0), (1,2), (1,3), (1,4), (2,0), (2,1), (2,3), (2,4)]
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({(1,0), (1,1), (1,3), (1,4), (2,2), (3,0), (3,4), (4,2), (4,3)} : Finset Cell) then 0 else 1,
   if x = (1,0) then 1 else 0⟩
private def constantPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 1, 2, 2, 1, 1, 0, 0, 1],
    ![0, 0, 0, 0, 3, 0, 2, 3, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 2, 0, 2, 1, 0, 0, 1],
    ![0, 0, 0, 0, 1, 3, 2, 0, 1, 1, 1, 0],
    ![1, 3, 2, 1, 0, 0, 0, 0, 0, 2, 3, 2],
    ![2, 0, 2, 3, 0, 0, 0, 0, 3, 2, 2, 3],
    ![2, 2, 0, 2, 0, 0, 0, 0, 3, 2, 0, 3],
    ![1, 3, 2, 0, 0, 0, 0, 0, 2, 2, 3, 0],
    ![1, 0, 1, 1, 0, 3, 3, 2, 0, 0, 0, 0],
    ![0, 0, 0, 1, 2, 2, 2, 2, 0, 0, 0, 0],
    ![0, 0, 0, 1, 3, 2, 0, 3, 0, 0, 0, 0],
    ![1, 0, 1, 0, 2, 3, 3, 0, 0, 0, 0, 0]]
private def linearPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def leftChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, -18, 12, -24, 3, -15, 9, 15, -9, 51, -18, 3],
    ![0, 12, -16, -16, -4, 8, 0, 4, 24, -80, 36, 32],
    ![0, -24, -16, -16, -4, 8, 0, 4, -12, 64, 0, -4],
    ![0, 3, -4, -4, -1, 2, 0, 1, -21, 7, 9, 17],
    ![0, -15, 8, 8, 2, -4, 0, -2, 6, -5, 9, 2],
    ![0, 9, 0, 0, 0, 0, 0, 0, 0, 27, -27, 0],
    ![0, 15, 4, 4, 1, -2, 0, -1, 21, -25, 9, -17],
    ![0, -9, 24, -12, -21, 6, 0, 21, -9, 39, -27, -3],
    ![0, 51, -80, 64, 7, -5, 27, -25, 39, -184, 99, 7],
    ![0, -18, 36, 0, 9, 9, -27, 9, -27, 99, -54, -27],
    ![0, 3, 32, -4, 17, 2, 0, -17, -3, 7, -27, -1],
    ![1, 0, -1, 0, 0, 0, 0, 0, 0, -1, 1, 0]]
private def rightChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]
private def leftTimesConstant : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![72, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 72, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 72, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 72, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 72, 0, 0, 0],
    ![72, 0, 0, 0, 0, 0, 0, 0, 0, 72, 0, 0],
    ![-72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72],
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
      if i=j ∧ i≠11 then (72 : ℤ) else 0 := by
  rw [left_check]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem slope_check : (leftChange * linearPart * rightChange) 11 11 ≠ 0 := by decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem cover_check : ∀ j ∈ twelveShape 5, ∃ i, directions i = j := by decide +kernel

theorem twelve_odd_5 (K : Type*) [Field K] [CharZero K] : HasOddBlock K (twelveShape 5) :=
  odd_block_of_integers _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries 72 (by decide) diagonal_check slope_check

#print axioms twelve_odd_5
end PermanentFive
