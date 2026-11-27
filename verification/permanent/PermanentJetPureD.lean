import PermanentIntegralJet
import PermanentTwelveShapes

/-! Integer row and column operations certify the first-order determinant
on the twelve directions below. The last diagonal first derivative is 8. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 12 → Cell :=
  ![(0,1), (0,2), (0,3), (0,4), (1,1), (1,2), (1,3), (1,4), (2,1), (2,2), (2,3), (2,4)]
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({(0,1), (0,2), (3,1), (3,2), (3,3), (4,3)} : Finset Cell) then 0 else 1,
   if x = (0,1) then 1 else 0⟩
private def constantPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 2, 4, 1, 0, 2, 4, 1],
    ![0, 0, 0, 0, 2, 0, 4, 1, 2, 0, 4, 1],
    ![0, 0, 0, 0, 4, 4, 0, 2, 4, 4, 0, 2],
    ![0, 0, 0, 0, 1, 1, 2, 0, 1, 1, 2, 0],
    ![0, 2, 4, 1, 0, 0, 0, 0, 0, 2, 2, 1],
    ![2, 0, 4, 1, 0, 0, 0, 0, 2, 0, 2, 1],
    ![4, 4, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0],
    ![1, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    ![0, 2, 4, 1, 0, 2, 2, 1, 0, 0, 0, 0],
    ![2, 0, 4, 1, 2, 0, 2, 1, 0, 0, 0, 0],
    ![4, 4, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0],
    ![1, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0]]
private def linearPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]
private def leftChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![14, -4, -2, -14, -12, 6, 0, 18, -12, 6, 6, 6],
    ![-4, 14, -2, -14, 6, -12, 0, 18, 6, -12, 6, 6],
    ![-2, -2, -1, 2, 3, 3, 0, 0, 3, 3, -6, 12],
    ![-14, -14, 2, 32, 12, 12, 0, -36, 12, 12, 12, -60],
    ![-12, 6, 3, 12, 9, -9, 0, -18, -9, 9, 0, 18],
    ![6, -12, 3, 12, -9, 9, 0, -18, 9, -9, 0, 18],
    ![18, 18, 0, -36, -18, -18, 0, 36, 18, 18, 0, -36],
    ![-12, 6, 3, 12, -9, 9, 0, 18, 9, -9, 0, -18],
    ![6, -12, 3, 12, 9, -9, 0, 18, -9, 9, 0, -18],
    ![6, 6, -6, 12, 0, 0, 0, 0, 0, 0, 0, 0],
    ![6, 6, 12, -60, 18, 18, 0, -36, -18, -18, 0, 36],
    ![0, 0, 0, 0, 0, 0, 1, -2, 0, 0, -1, 2]]
private def rightChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -2],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2]]
private def leftTimesConstant : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 72, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 144, 72, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 72, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 0, 0],
    ![0, 0, 0, 0, 0, 0, 72, 0, 0, 0, 72, 0],
    ![0, 0, 0, 0, 0, 0, -144, 0, 0, 0, 0, 72],
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
private theorem cover_check : ∀ j ∈ twelveShape 3, ∃ i, directions i = j := by decide +kernel

theorem twelve_odd_3 (K : Type*) [Field K] [CharZero K] : HasOddBlock K (twelveShape 3) :=
  odd_block_of_integers _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries 72 (by decide) diagonal_check slope_check

#print axioms twelve_odd_3
end PermanentFive
