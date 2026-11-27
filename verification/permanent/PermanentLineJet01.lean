import PermanentIntegralJet
import PermanentLineBoards

/-! Integer row and column operations certify the first-order determinant
on the 10 directions below. The last diagonal first derivative is 60. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 10 → Cell :=
  ![(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,3), (2,4), (3,4)]
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({(0,0), (0,3), (1,1), (1,3), (2,0), (3,1), (3,2), (4,3)} : Finset Cell) then 0 else 1,
   if x = (0,0) then 1 else 0⟩
private def constantPart : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 3, 3, 2, 1, 1],
    ![0, 0, 0, 0, 3, 0, 3, 3, 2, 2],
    ![0, 0, 0, 0, 3, 3, 0, 3, 1, 1],
    ![0, 0, 0, 0, 2, 3, 3, 0, 1, 3],
    ![0, 3, 3, 2, 0, 0, 0, 0, 2, 2],
    ![3, 0, 3, 3, 0, 0, 0, 0, 1, 1],
    ![3, 3, 0, 3, 0, 0, 0, 0, 1, 1],
    ![2, 3, 3, 0, 0, 0, 0, 0, 2, 2],
    ![1, 2, 1, 1, 2, 1, 1, 2, 0, 0],
    ![1, 2, 1, 3, 2, 1, 1, 2, 0, 0]]
private def linearPart : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 2, 0, 0]]
private def leftChange : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 18, 18, -18, 54, -54],
    ![0, -4, -4, 0, 0, -16, 4, 12, 0, 12],
    ![0, -4, -4, 0, 0, 8, -20, 12, 0, 12],
    ![0, 0, 0, 0, 0, 0, 0, 0, -36, 36],
    ![18, -16, 8, 0, 0, -1, 1, 3, -9, 3],
    ![18, 4, -20, 0, 0, 1, -1, -3, 9, -3],
    ![-18, 12, 12, 0, 0, 3, -3, -9, 27, -9],
    ![54, 0, 0, -36, 0, -9, 9, 27, -81, 27],
    ![-54, 12, 12, 36, 0, 3, -3, -9, 27, -9],
    ![0, 0, 0, 0, 2, 1, 1, -3, 5, -5]]
private def rightChange : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, -3],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 5],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, -5]]
private def leftTimesConstant : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![72, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 72, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 72, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 72, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -36, 72, 0, 0, 0, 0],
    ![0, 0, 0, 0, -36, 0, 72, 0, 0, 0],
    ![0, 0, 0, 0, 108, 0, 0, 72, 0, 0],
    ![0, 0, 0, 0, -180, 0, 0, 0, 72, 0],
    ![0, 0, 0, 0, 180, 0, 0, 0, 0, 72],
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
      if i=j ∧ i≠9 then (72 : ℤ) else 0 := by
  rw [left_check]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem slope_check : (leftChange * linearPart * rightChange) 9 9 ≠ 0 := by decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem cover_check : ∀ j ∈ lineTen 1, ∃ i, directions i = j := by decide +kernel

theorem line_ten_odd_1 (K : Type*) [Field K] [CharZero K] : HasSimpleZeroBlock K 10 (lineTen 1) :=
  simple_zero_of_integers 9 _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries 72 (by decide) diagonal_check slope_check

#print axioms line_ten_odd_1
end PermanentFive
