import PermanentIntegralJet
import PermanentTwelveShapes

/-! Integer row and column operations certify the first-order determinant
on the twelve directions below. The last diagonal first derivative is -12. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 12 → Cell :=
  ![(0,0), (0,2), (0,3), (0,4), (1,0), (1,1), (1,2), (1,3), (1,4), (2,0), (3,0), (4,0)]
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({(0,0), (1,1), (1,2), (3,0), (3,2), (3,4), (4,3)} : Finset Cell) then 0 else 1,
   if x = (0,2) then 1 else 0⟩
private def constantPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 2, 3, 2, 3, 0, 0, 0],
    ![0, 0, 0, 0, 3, 2, 0, 2, 3, 2, 3, 3],
    ![0, 0, 0, 0, 2, 0, 2, 0, 2, 1, 2, 1],
    ![0, 0, 0, 0, 3, 2, 3, 2, 0, 1, 2, 1],
    ![0, 3, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 0, 2, 0, 0, 0, 0, 0, 2, 4, 2],
    ![3, 0, 2, 3, 0, 0, 0, 0, 0, 3, 4, 4],
    ![2, 2, 0, 2, 0, 0, 0, 0, 0, 2, 6, 2],
    ![3, 3, 2, 0, 0, 0, 0, 0, 0, 3, 4, 4],
    ![0, 2, 1, 1, 0, 2, 3, 2, 3, 0, 0, 0],
    ![0, 3, 2, 2, 0, 4, 4, 6, 4, 0, 0, 0],
    ![0, 3, 1, 1, 0, 2, 4, 2, 4, 0, 0, 0]]
private def linearPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2],
    ![0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0]]
private def leftChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 36, -108, 36, 72, 72, -84, -18, 48, -396, 0, 324],
    ![0, -108, 324, -108, 108, -216, -72, 54, 180, 1188, 0, -972],
    ![0, 36, -108, 36, 72, 72, 132, -18, -168, -396, 0, 324],
    ![0, 72, 108, 72, 144, -18, -60, -36, -12, -144, 0, 0],
    ![0, 72, -216, 72, -18, 144, -114, -36, 42, 1800, -324, -972],
    ![0, -84, -72, 132, -60, -114, 124, 42, -40, -588, 0, 540],
    ![0, -18, 54, -18, -36, -36, 42, 9, -24, -1098, 324, 486],
    ![0, 48, 180, -168, -12, 42, -40, -24, -8, 336, 0, -216],
    ![0, -396, 1188, -396, -144, 1800, -588, -1098, 336, 4356, 0, -3564],
    ![0, 0, 0, 0, 0, -324, 0, 324, 0, 0, 0, 0],
    ![0, 324, -972, 324, 0, -972, 540, 486, -216, -3564, 0, 2916],
    ![-6, 0, 0, 0, -3, 0, 1, 0, -1, 6, 0, 0]]
private def rightChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -3],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]
private def leftTimesConstant : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 648, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 648, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 648, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-324, 0, 0, 0, 648, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 648, 0, 0, 0, 0, 0, 0],
    ![108, 0, 0, 0, 0, 0, 648, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 648, 0, 0, 0, 0],
    ![-108, 0, 0, 0, 0, 0, 0, 0, 648, 0, 0, 0],
    ![648, 0, 0, 0, 0, 0, 0, 0, 0, 648, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 648, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 648],
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
      if i=j ∧ i≠11 then (648 : ℤ) else 0 := by
  rw [left_check]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem slope_check : (leftChange * linearPart * rightChange) 11 11 ≠ 0 := by decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem cover_check : ∀ j ∈ twelveShape 7, ∃ i, directions i = j := by decide +kernel

theorem twelve_odd_7 (K : Type*) [Field K] [CharZero K] : HasOddBlock K (twelveShape 7) :=
  odd_block_of_integers _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries 648 (by decide) diagonal_check slope_check

#print axioms twelve_odd_7
end PermanentFive
