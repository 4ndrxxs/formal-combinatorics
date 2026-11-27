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
    ![0, 2, 2, 2, 2, 0, 0, 0],
    ![2, 3, 0, 3, 3, 0, 0, 0],
    ![2, 3, 3, 0, 2, 0, 0, 0],
    ![2, 3, 3, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 3],
    ![0, 0, 0, 0, 0, 0, 2, 2],
    ![0, 0, 0, 0, 0, 2, 3, 0]]
private def inverseNumerator : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of ![
    ![24, -90, 24, 18, 18, 0, 0, 0],
    ![-40, 24, 16, 12, 12, 0, 0, 0],
    ![16, 24, -40, 12, 12, 0, 0, 0],
    ![12, 18, 12, -54, 30, 0, 0, 0],
    ![12, 18, 12, 30, -54, 0, 0, 0],
    ![0, 0, 0, 0, 0, 42, -63, 42],
    ![0, 0, 0, 0, 0, -28, 42, 28],
    ![0, 0, 0, 0, 0, 28, 42, -28]]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem entries : ∀ i j : Fin 8,
    secondAt (boardPoint (lineAmbient 1)) (rows i) (cols j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem inverse_check : block * inverseNumerator = (168 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem line_ambient_1 (K : Type*) [Field K] [CharZero K] : HasAmbientEight K (lineAmbient 1) :=
  ambient_eight_of_integers K _ rows cols block entries
    (det_ne_zero_of_inverse_certificate block inverseNumerator 168 (by decide) inverse_check)

#print axioms line_ambient_1
end PermanentFive
