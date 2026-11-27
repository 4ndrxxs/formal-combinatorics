import PermanentIntegralJet
import PermanentTwelveShapes

/-! Integer row and column operations certify the first-order determinant
on the twelve directions below. The last diagonal first derivative is -4. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 12 → Cell :=
  ![(0,2), (0,3), (0,4), (1,0), (1,1), (1,3), (1,4), (2,0), (2,1), (2,2), (2,3), (2,4)]
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({(0,2), (0,3), (0,4), (1,1), (2,0), (2,2), (3,3), (4,4)} : Finset Cell) then 0 else 1,
   if x = (0,2) then 1 else 0⟩
private def constantPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 3, 2, 3, 3, 2, 3, 0, 3, 3],
    ![0, 0, 0, 3, 2, 0, 2, 3, 4, 3, 0, 4],
    ![0, 0, 0, 3, 2, 2, 0, 3, 4, 3, 4, 0],
    ![3, 3, 3, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![3, 0, 2, 0, 0, 0, 0, 1, 1, 2, 0, 4],
    ![3, 2, 0, 0, 0, 0, 0, 1, 1, 2, 4, 0],
    ![2, 3, 3, 0, 0, 1, 1, 0, 0, 0, 0, 0],
    ![3, 4, 4, 0, 0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 3, 3, 1, 1, 2, 2, 0, 0, 0, 0, 0],
    ![3, 0, 4, 1, 1, 0, 4, 0, 0, 0, 0, 0],
    ![3, 4, 0, 1, 1, 4, 0, 0, 0, 0, 0, 0]]
private def linearPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0],
    ![0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0]]
private def leftChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, -8, 8, -8, 4, 4],
    ![0, 4, -4, 0, 0, -4, 4, -12, 12, 4, -4, 0],
    ![0, -4, 4, 0, 0, 4, -4, -12, 12, 4, 0, -4],
    ![0, 0, 0, 0, 0, 0, 0, -168, 104, 24, 4, 4],
    ![0, -4, 4, 0, 0, 4, -4, 60, -44, -4, 0, 4],
    ![0, 4, -4, 0, 0, -4, 4, 60, -44, -4, 4, 0],
    ![-8, -12, -12, 0, -168, 60, 60, -312, 232, 96, -16, -16],
    ![8, 12, 12, 0, 104, -44, -44, 232, -152, -80, 8, 8],
    ![-8, 4, 4, 0, 24, -4, -4, 96, -80, -8, 4, 4],
    ![4, -4, 0, 0, 4, 0, 4, -16, 8, 4, -1, -3],
    ![4, 0, -4, 0, 4, 4, 0, -16, 8, 4, -3, -1],
    ![0, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0, 0]]
private def rightChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]
private def leftTimesConstant : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 32, 32, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0],
    ![0, 0, 0, -32, 0, 0, 0, 32, 0, 0, 0, 0],
    ![0, 0, 0, 32, 0, 0, 0, 0, 32, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32],
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
      if i=j ∧ i≠11 then (32 : ℤ) else 0 := by
  rw [left_check]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem slope_check : (leftChange * linearPart * rightChange) 11 11 ≠ 0 := by decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem cover_check : ∀ j ∈ twelveShape 2, ∃ i, directions i = j := by decide +kernel

theorem twelve_odd_2 (K : Type*) [Field K] [CharZero K] : HasOddBlock K (twelveShape 2) :=
  odd_block_of_integers _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries 32 (by decide) diagonal_check slope_check

#print axioms twelve_odd_2
end PermanentFive
