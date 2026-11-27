import PermanentAmbientEight
import PermanentLineBoards

/-! An eight-by-eight nonsingular ambient minor at the board indicator. -/

namespace PermanentFive
open Matrix QuinticPencil
private def rows : Fin 8 → Cell := ![(4,1), (4,0), (4,2), (4,3), (4,4), (3,1), (3,0), (3,2)]
private def cols : Fin 8 → Cell := ![(3,0), (3,1), (3,2), (3,3), (3,4), (4,0), (4,1), (4,2)]
private def block : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of ![
    ![2, 0, 3, 3, 3, 0, 0, 0],
    ![0, 2, 3, 3, 3, 0, 0, 0],
    ![3, 3, 0, 4, 4, 0, 0, 0],
    ![3, 3, 4, 0, 4, 0, 0, 0],
    ![3, 3, 4, 4, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 3],
    ![0, 0, 0, 0, 0, 0, 2, 3],
    ![0, 0, 0, 0, 0, 3, 3, 0]]
private def inverseNumerator : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of ![
    ![99, -243, 54, 54, 54, 0, 0, 0],
    ![-243, 99, 54, 54, 54, 0, 0, 0],
    ![54, 54, -126, 45, 45, 0, 0, 0],
    ![54, 54, 45, -126, 45, 0, 0, 0],
    ![54, 54, 45, 45, -126, 0, 0, 0],
    ![0, 0, 0, 0, 0, 171, -171, 114],
    ![0, 0, 0, 0, 0, -171, 171, 114],
    ![0, 0, 0, 0, 0, 114, 114, -76]]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem entries : ∀ i j : Fin 8,
    secondAt (boardPoint (lineAmbient 3)) (rows i) (cols j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem inverse_check : block * inverseNumerator = (684 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem line_ambient_3 (K : Type*) [Field K] [CharZero K] : HasAmbientEight K (lineAmbient 3) :=
  ambient_eight_of_integers K _ rows cols block entries
    (det_ne_zero_of_inverse_certificate block inverseNumerator 684 (by decide) inverse_check)

#print axioms line_ambient_3
end PermanentFive
