import PermanentIntegralJet
import PermanentTwelveShapes

/-! Integer row and column operations certify the first-order determinant
on the twelve directions below. The last diagonal first derivative is 72. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 12 → Cell :=
  ![(0,2), (0,3), (0,4), (1,1), (1,2), (1,3), (1,4), (2,0), (2,1), (2,2), (2,3), (2,4)]
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({(0,2)} : Finset Cell) then 0 else 1,
   if x = (0,0) then 1 else 0⟩
private def constantPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 6, 0, 6, 6, 6, 6, 0, 6, 6],
    ![0, 0, 0, 6, 6, 0, 6, 6, 6, 6, 0, 6],
    ![0, 0, 0, 6, 6, 6, 0, 6, 6, 6, 6, 0],
    ![6, 6, 6, 0, 0, 0, 0, 4, 0, 6, 4, 4],
    ![0, 6, 6, 0, 0, 0, 0, 6, 6, 0, 6, 6],
    ![6, 0, 6, 0, 0, 0, 0, 4, 4, 6, 0, 4],
    ![6, 6, 0, 0, 0, 0, 0, 4, 4, 6, 4, 0],
    ![6, 6, 6, 4, 6, 4, 4, 0, 0, 0, 0, 0],
    ![6, 6, 6, 0, 6, 4, 4, 0, 0, 0, 0, 0],
    ![0, 6, 6, 6, 0, 6, 6, 0, 0, 0, 0, 0],
    ![6, 0, 6, 4, 6, 0, 4, 0, 0, 0, 0, 0],
    ![6, 6, 0, 4, 6, 4, 0, 0, 0, 0, 0, 0]]
private def linearPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0]]
private def leftChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 4, -4, 0, 0, -6, 6, 108, -36, -24, -42, -30],
    ![0, -4, 4, 0, 0, 6, -6, 108, -36, -24, -30, -42],
    ![0, 0, 0, 0, 0, 0, 0, 36, -36, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -48, 24, 0, 24, 24],
    ![0, -6, 6, 0, 0, 9, -9, -126, 54, 36, 27, 45],
    ![0, 6, -6, 0, 0, -9, 9, -126, 54, 36, 45, 27],
    ![0, 108, 108, 36, -48, -126, -126, 2484, -792, -600, -954, -954],
    ![0, -36, -36, -36, 24, 54, 54, -792, 252, 192, 306, 306],
    ![0, -24, -24, 0, 0, 36, 36, -600, 192, 144, 228, 228],
    ![0, -42, -30, 0, 24, 27, 45, -954, 306, 228, 369, 351],
    ![0, -30, -42, 0, 24, 45, 27, -954, 306, 228, 351, 369],
    ![-1, 0, 0, 0, 1, 0, 0, -18, 6, 5, 6, 6]]
private def rightChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -18],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 6],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 5],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 6],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 6]]
private def leftTimesConstant : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0],
    ![144, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0],
    ![-2592, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0],
    ![864, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0],
    ![720, 0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0],
    ![864, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144, 0],
    ![864, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144],
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
      if i=j ∧ i≠11 then (144 : ℤ) else 0 := by
  rw [left_check]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem slope_check : (leftChange * linearPart * rightChange) 11 11 ≠ 0 := by decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem cover_check : ∀ j ∈ twelveShape 1, ∃ i, directions i = j := by decide +kernel

theorem twelve_odd_1 (K : Type*) [Field K] [CharZero K] : HasOddBlock K (twelveShape 1) :=
  odd_block_of_integers _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries 144 (by decide) diagonal_check slope_check

#print axioms twelve_odd_1
end PermanentFive
