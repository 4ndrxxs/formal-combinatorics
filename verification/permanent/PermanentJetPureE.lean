import PermanentIntegralJet
import PermanentTwelveShapes

/-! Integer row and column operations certify the first-order determinant
on the twelve directions below. The last diagonal first derivative is 8. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 12 → Cell :=
  ![(0,1), (0,2), (0,3), (0,4), (1,1), (1,2), (1,3), (1,4), (2,0), (2,2), (2,3), (2,4)]
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({(1,3), (2,1), (3,3), (4,3)} : Finset Cell) then 0 else 1,
   if x = (1,3) then 1 else 0⟩
private def constantPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 2, 6, 2, 0, 0, 6, 0],
    ![0, 0, 0, 0, 2, 0, 4, 2, 0, 0, 6, 0],
    ![0, 0, 0, 0, 6, 4, 0, 4, 6, 6, 0, 6],
    ![0, 0, 0, 0, 2, 2, 4, 0, 0, 0, 6, 0],
    ![0, 2, 6, 2, 0, 0, 0, 0, 2, 2, 6, 2],
    ![2, 0, 4, 2, 0, 0, 0, 0, 2, 0, 6, 2],
    ![6, 4, 0, 4, 0, 0, 0, 0, 6, 6, 0, 6],
    ![2, 2, 4, 0, 0, 0, 0, 0, 2, 2, 6, 0],
    ![0, 0, 6, 0, 2, 2, 6, 2, 0, 0, 0, 0],
    ![0, 0, 6, 0, 2, 0, 6, 2, 0, 0, 0, 0],
    ![6, 6, 0, 6, 6, 6, 0, 6, 0, 0, 0, 0],
    ![0, 0, 6, 0, 2, 2, 6, 0, 0, 0, 0, 0]]
private def linearPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
private def leftChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![-225, 0, -66, 270, -45, 0, 81, 0, 633, -159, -39, -429],
    ![-66, 0, -16, 54, 12, 0, 12, 0, 184, -50, -12, -104],
    ![270, 0, 54, -324, 54, 0, -72, 0, -810, 216, 72, 540],
    ![-45, 0, 12, 54, -9, 0, -9, 0, -75, 69, 9, 15],
    ![0, 0, 0, 0, 0, 0, 0, 0, 126, -126, 0, 0],
    ![81, 0, 12, -72, -9, 0, -9, 0, -201, 69, 9, 141],
    ![0, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, -126],
    ![633, 0, 184, -810, -75, 126, -201, 126, -1801, 449, 117, 1259],
    ![-159, 0, -50, 216, 69, -126, 69, 0, 449, -109, -27, -325],
    ![-39, 0, -12, 72, 9, 0, 9, 0, 117, -27, -9, -99],
    ![-429, 0, -104, 540, 15, 0, 141, -126, 1259, -325, -99, -865],
    ![0, 1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 1]]
private def rightChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]]
private def leftTimesConstant : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![252, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 252, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 252, 0, 252, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 252, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 252, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 252, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 252, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 252, 0, 0, 0],
    ![0, 252, 0, 0, 0, 0, 0, 0, 0, 252, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252, 0],
    ![0, -252, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252],
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
      if i=j ∧ i≠11 then (252 : ℤ) else 0 := by
  rw [left_check]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem slope_check : (leftChange * linearPart * rightChange) 11 11 ≠ 0 := by decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem cover_check : ∀ j ∈ twelveShape 4, ∃ i, directions i = j := by decide +kernel

theorem twelve_odd_4 (K : Type*) [Field K] [CharZero K] : HasOddBlock K (twelveShape 4) :=
  odd_block_of_integers _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries 252 (by decide) diagonal_check slope_check

#print axioms twelve_odd_4
end PermanentFive
