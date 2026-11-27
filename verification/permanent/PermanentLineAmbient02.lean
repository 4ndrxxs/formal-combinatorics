import PermanentAmbientEight
import PermanentLineBoards

/-! An eight-by-eight nonsingular ambient minor at the board indicator. -/

namespace PermanentFive
open Matrix QuinticPencil
private def rows : Fin 8 → Cell := ![(3,1), (3,0), (3,2), (3,4), (2,1), (2,0), (2,2), (2,4)]
private def cols : Fin 8 → Cell := ![(2,0), (2,1), (2,2), (2,4), (3,0), (3,1), (3,2), (3,4)]
private def block : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of ![
    ![1, 0, 1, 2, 0, 0, 0, 0],
    ![0, 1, 1, 2, 0, 0, 0, 0],
    ![1, 1, 0, 2, 0, 0, 0, 0],
    ![2, 2, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 2],
    ![0, 0, 0, 0, 0, 1, 1, 2],
    ![0, 0, 0, 0, 1, 1, 0, 2],
    ![0, 0, 0, 0, 2, 2, 2, 0]]
private def inverseNumerator : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of ![
    ![2, -4, 2, 1, 0, 0, 0, 0],
    ![-4, 2, 2, 1, 0, 0, 0, 0],
    ![2, 2, -4, 1, 0, 0, 0, 0],
    ![1, 1, 1, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, -4, 2, 1],
    ![0, 0, 0, 0, -4, 2, 2, 1],
    ![0, 0, 0, 0, 2, 2, -4, 1],
    ![0, 0, 0, 0, 1, 1, 1, -1]]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem entries : ∀ i j : Fin 8,
    secondAt (boardPoint (lineAmbient 2)) (rows i) (cols j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem inverse_check : block * inverseNumerator = (6 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem line_ambient_2 (K : Type*) [Field K] [CharZero K] : HasAmbientEight K (lineAmbient 2) :=
  ambient_eight_of_integers K _ rows cols block entries
    (det_ne_zero_of_inverse_certificate block inverseNumerator 6 (by decide) inverse_check)

#print axioms line_ambient_2
end PermanentFive
