import PermanentIntegralJet
import PermanentLineBoards

/-! Integer row and column operations certify the first-order determinant
on the 10 directions below. The last diagonal first derivative is -64. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 10 → Cell :=
  ![(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,4), (2,2), (3,2), (4,2)]
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({(0,4), (2,1), (2,4), (3,2), (4,3)} : Finset Cell) then 0 else 1,
   if x = (0,0) then 1 else 0⟩
private def constantPart : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 2, 2, 4, 2, 2],
    ![0, 0, 0, 0, 2, 0, 3, 4, 3, 4],
    ![0, 0, 0, 0, 2, 3, 3, 0, 0, 0],
    ![0, 0, 0, 0, 2, 3, 3, 6, 2, 2],
    ![0, 2, 2, 2, 0, 0, 0, 3, 1, 1],
    ![2, 0, 3, 3, 0, 0, 0, 3, 2, 2],
    ![2, 3, 3, 3, 0, 0, 0, 4, 3, 4],
    ![4, 4, 0, 6, 3, 3, 4, 0, 0, 0],
    ![2, 3, 0, 2, 1, 2, 3, 0, 0, 0],
    ![2, 4, 0, 2, 1, 2, 4, 0, 0, 0]]
private def linearPart : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]]
private def leftChange : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![-36, 0, -30, 30, -36, 24, 0, -24, 120, -48],
    ![-30, 0, 23, 1, 18, 20, 0, -28, 44, -8],
    ![30, 0, 1, -25, 30, -20, 0, 28, -44, 8],
    ![-36, 0, 18, 30, -36, 24, 0, 24, -120, 48],
    ![24, 0, 20, -20, 24, -16, 0, -16, 176, -128],
    ![0, 0, 0, 0, 0, 0, 0, 0, -96, 96],
    ![-24, 0, -28, 28, 24, -16, 0, -16, 80, -32],
    ![120, 0, 44, -44, -120, 176, -96, 80, -400, 160],
    ![-48, 0, -8, 8, 48, -128, 96, -32, 160, -64],
    ![0, 4, -1, -3, 6, 0, -4, -4, 32, -20]]
private def rightChange : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, -3],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 6],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, -4],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, -4],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 32],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, -20]]
private def leftTimesConstant : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of ![
    ![96, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 24, 96, 0, 0, 0, 0, 0, 0, 0],
    ![0, 72, 0, 96, 0, 0, 0, 0, 0, 0],
    ![0, -144, 0, 0, 96, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 96, 0, 0, 0, 0],
    ![0, 96, 0, 0, 0, 0, 96, 0, 0, 0],
    ![0, 96, 0, 0, 0, 0, 0, 96, 0, 0],
    ![0, -768, 0, 0, 0, 0, 0, 0, 96, 0],
    ![0, 480, 0, 0, 0, 0, 0, 0, 0, 96],
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
      if i=j ∧ i≠9 then (96 : ℤ) else 0 := by
  rw [left_check]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem slope_check : (leftChange * linearPart * rightChange) 9 9 ≠ 0 := by decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem cover_check : ∀ j ∈ lineTen 8, ∃ i, directions i = j := by decide +kernel

theorem line_ten_odd_8 (K : Type*) [Field K] [CharZero K] : HasSimpleZeroBlock K 10 (lineTen 8) :=
  simple_zero_of_integers 9 _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries 96 (by decide) diagonal_check slope_check

#print axioms line_ten_odd_8
end PermanentFive
