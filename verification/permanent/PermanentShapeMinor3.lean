import PermanentShapeFamily

/-! A rank-9 minor at the indicator of the 7-cell sparse pattern. -/

namespace PermanentFive
open Matrix QuinticPencil
private def rows : Fin 9 → Cell := ![(3,2), (3,1), (3,3), (2,2), (2,1), (2,3), (4,2), (4,1), (4,3)]
private def cols : Fin 9 → Cell := ![(2,1), (2,2), (2,3), (3,1), (3,2), (3,3), (4,1), (4,2), (4,3)]
private def block : Matrix (Fin 9) (Fin 9) ℤ :=
  Matrix.of ![
    ![1, 0, 1, 0, 0, 0, 1, 0, 1],
    ![0, 1, 1, 0, 0, 0, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 1, 0, 1, 1, 0, 1],
    ![0, 0, 0, 0, 1, 1, 0, 1, 1],
    ![0, 0, 0, 1, 1, 0, 1, 1, 0],
    ![1, 0, 1, 1, 0, 1, 0, 0, 0],
    ![0, 1, 1, 0, 1, 1, 0, 0, 0],
    ![1, 1, 0, 1, 1, 0, 0, 0, 0]]
private def inverseNumerator : Matrix (Fin 9) (Fin 9) ℤ :=
  Matrix.of ![
    ![1, -1, 1, -1, 1, -1, 1, -1, 1],
    ![-1, 1, 1, 1, -1, -1, -1, 1, 1],
    ![1, 1, -1, -1, -1, 1, 1, 1, -1],
    ![-1, 1, -1, 1, -1, 1, 1, -1, 1],
    ![1, -1, -1, -1, 1, 1, -1, 1, 1],
    ![-1, -1, 1, 1, 1, -1, 1, 1, -1],
    ![1, -1, 1, 1, -1, 1, -1, 1, -1],
    ![-1, 1, 1, -1, 1, 1, 1, -1, -1],
    ![1, 1, -1, 1, 1, -1, -1, -1, 1]]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem entries : ∀ i j : Fin 9,
    secondAt (boardPoint (shapePattern 3)) (rows i) (cols j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem inverse_check : block * inverseNumerator = (4 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem shape_minor_3 (K : Type*) [Field K] [CharZero K] :
    AmbientWitness K (shapePattern 3) (shapeRank 3) :=
  ambient_of_integer_minor K _ rows cols block entries
    (det_ne_zero_of_inverse_certificate block inverseNumerator 4 (by decide) inverse_check)

#print axioms shape_minor_3
end PermanentFive
