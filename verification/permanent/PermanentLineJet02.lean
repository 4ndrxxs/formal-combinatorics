import PermanentIntegralJet
import PermanentLineBoards

/-! Integer row and column operations certify the first-order determinant
on the 10 directions below. The last diagonal first derivative is 12. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 10 → Cell :=
  ![(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,4), (2,0), (3,0)]
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({(0,3), (0,4), (1,3), (2,1), (2,3), (2,4), (3,4), (4,0), (4,2)} : Finset Cell) then 0 else 1,
   if x = (2,1) then 1 else 0⟩
private def constantPart : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 1, 0, 2, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 2, 2, 1],
    ![0, 0, 0, 0, 0, 1, 0, 2, 3, 0],
    ![0, 0, 0, 0, 1, 2, 1, 2, 3, 2],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 2, 0, 0, 0, 0, 1, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 1, 0],
    ![2, 2, 2, 2, 0, 0, 0, 0, 3, 1],
    ![0, 2, 3, 3, 0, 1, 1, 3, 0, 0],
    ![0, 1, 0, 2, 0, 0, 0, 1, 0, 0]]
private def linearPart : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 1, 0, 1],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 1, 0, 0]]
private def leftChange : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 1, 2, -1, 16, -2, -6, 1, 0, -4],
    ![0, 2, 4, -2, 24, 4, -20, 2, 0, -8],
    ![0, -1, -2, 1, -8, 2, 6, -1, 0, 4],
    ![0, 16, 24, -8, 160, 24, -104, 0, -8, -40],
    ![0, -2, 4, 2, 24, 4, -12, -2, 0, -8],
    ![0, -6, -20, 6, -104, -12, 84, -6, 8, 16],
    ![0, 1, 2, -1, 0, -2, -6, 1, 0, 4],
    ![0, 0, 0, 0, -8, 0, 8, 0, 0, 0],
    ![0, -4, -8, 4, -40, -8, 16, 4, 0, 16],
    ![1, 0, -1, 0, -3, 0, 3, 0, 0, 0]]
private def rightChange : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, -3],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 3],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]
private def leftTimesConstant : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 8, 0, 0, 0, 0, 0, 0, 0, 0],
    ![8, 0, 8, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 8, 0, 0, 0, 0, 0, 0],
    ![24, 0, 0, 0, 8, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 8, 0, 0, 0, 0],
    ![-24, 0, 0, 0, 0, 0, 8, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 8, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 8],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem entries : ∀ i j : Fin 10,
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
private theorem diagonal_check : ∀ i j : Fin 10,
    (leftChange * constantPart * rightChange) i j =
      if i=j ∧ i≠9 then (8 : ℤ) else 0 := by
  rw [left_check]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem slope_check : (leftChange * linearPart * rightChange) 9 9 ≠ 0 := by decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem cover_check : ∀ j ∈ lineTen 2, ∃ i, directions i = j := by decide +kernel

theorem line_ten_odd_2 (K : Type*) [Field K] [CharZero K] : HasSimpleZeroBlock K 10 (lineTen 2) :=
  simple_zero_of_integers 9 _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries 8 (by decide) diagonal_check slope_check

#print axioms line_ten_odd_2
end PermanentFive
