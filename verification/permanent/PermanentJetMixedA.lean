import PermanentIntegralJet
import PermanentTwelveShapes

/-! Integer row and column operations certify the first-order determinant
on the twelve directions below. The last diagonal first derivative is 24. -/

namespace PermanentFive
open Matrix QuinticPencil
private def directions : Fin 12 → Cell :=
  ![(0,1), (0,2), (0,3), (0,4), (1,0), (1,1), (1,2), (1,3), (1,4), (2,0), (3,0), (4,0)]
private def centre (x : Cell) : DualNumber ℤ :=
  ⟨if x ∈ ({(0,2), (0,4), (1,2), (2,1), (4,3)} : Finset Cell) then 0 else 1,
   if x = (0,2) then 1 else 0⟩
private def constantPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 4, 0, 4, 6, 4, 3, 3, 4],
    ![0, 0, 0, 0, 3, 4, 0, 4, 3, 4, 3, 4],
    ![0, 0, 0, 0, 4, 6, 4, 0, 4, 4, 3, 3],
    ![0, 0, 0, 0, 3, 4, 3, 4, 0, 3, 2, 3],
    ![4, 3, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 6, 4, 0, 0, 0, 0, 0, 2, 2, 2],
    ![4, 0, 4, 3, 0, 0, 0, 0, 0, 3, 2, 3],
    ![6, 4, 0, 4, 0, 0, 0, 0, 0, 2, 2, 2],
    ![4, 3, 4, 0, 0, 0, 0, 0, 0, 3, 2, 3],
    ![3, 4, 4, 3, 0, 2, 3, 2, 3, 0, 0, 0],
    ![3, 3, 3, 2, 0, 2, 2, 2, 2, 0, 0, 0],
    ![4, 4, 3, 3, 0, 2, 3, 2, 3, 0, 0, 0]]
private def linearPart : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0]]
private def leftChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![81, -108, 81, -108, 153, 0, 99, -108, 36, -1719, 891, 1017],
    ![-108, 144, -108, 144, 144, 0, -480, 144, 300, 900, -1188, 36],
    ![81, -108, 81, -108, 153, 0, 99, -108, 36, 369, 891, -1071],
    ![-108, 144, -108, 144, 144, 0, 216, 144, -396, 900, -1188, 36],
    ![153, 144, 153, 144, 1449, 0, -393, -378, -48, -927, -1449, 1341],
    ![99, -480, 99, 216, -393, 0, 121, 42, 44, 219, 45, -33],
    ![-108, 144, -108, 144, -378, 0, 42, 144, -222, -144, 1944, -1008],
    ![36, 300, 36, -396, -48, 0, 44, -222, 16, -300, -648, 1032],
    ![-1719, 900, 369, 900, -927, 0, 219, -144, -300, -639, 1971, 225],
    ![891, -1188, 891, -1188, -1449, 0, 45, 1944, -648, 1971, 9801, -9693],
    ![1017, 36, -1071, 36, 1341, 0, -33, -1008, 1032, 225, -9693, 6273],
    ![0, 0, 0, 0, 0, 1, 0, -1, 0, -6, 0, 6]]
private def rightChange : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -6],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 6]]
private def leftTimesConstant : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of ![
    ![2088, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2088, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2088, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2088, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2088, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 2088, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2088, 0, 2088, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2088, 0, 0, 0],
    ![0, 0, 0, 0, 0, 12528, 0, 0, 0, 2088, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2088, 0],
    ![0, 0, 0, 0, 0, -12528, 0, 0, 0, 0, 0, 2088],
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
      if i=j ∧ i≠11 then (2088 : ℤ) else 0 := by
  rw [left_check]
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem slope_check : (leftChange * linearPart * rightChange) 11 11 ≠ 0 := by decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem cover_check : ∀ j ∈ twelveShape 6, ∃ i, directions i = j := by decide +kernel

theorem twelve_odd_6 (K : Type*) [Field K] [CharZero K] : HasOddBlock K (twelveShape 6) :=
  odd_block_of_integers _ directions cover_check centre constantPart linearPart leftChange rightChange
    entries 2088 (by decide) diagonal_check slope_check

#print axioms twelve_odd_6
end PermanentFive
