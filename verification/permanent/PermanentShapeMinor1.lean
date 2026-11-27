import PermanentShapeFamily

/-! A rank-8 minor at the indicator of the 7-cell sparse pattern. -/

namespace PermanentFive
open Matrix QuinticPencil
private def rows : Fin 8 → Cell := ![(4,1), (4,0), (4,2), (4,3), (3,1), (3,0), (3,2), (3,3)]
private def cols : Fin 8 → Cell := ![(3,0), (3,1), (3,2), (3,3), (4,0), (4,1), (4,2), (4,3)]
private def block : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of ![
    ![1, 0, 1, 1, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 0, 0],
    ![1, 1, 0, 2, 0, 0, 0, 0],
    ![1, 1, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 1],
    ![0, 0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 1, 1, 0, 2],
    ![0, 0, 0, 0, 1, 1, 2, 0]]
private def inverseNumerator : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of ![
    ![0, -2, 1, 1, 0, 0, 0, 0],
    ![-2, 0, 1, 1, 0, 0, 0, 0],
    ![1, 1, -1, 0, 0, 0, 0, 0],
    ![1, 1, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -2, 1, 1],
    ![0, 0, 0, 0, -2, 0, 1, 1],
    ![0, 0, 0, 0, 1, 1, -1, 0],
    ![0, 0, 0, 0, 1, 1, 0, -1]]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem entries : ∀ i j : Fin 8,
    secondAt (boardPoint (shapePattern 1)) (rows i) (cols j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem inverse_check : block * inverseNumerator = (2 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem shape_minor_1 (K : Type*) [Field K] [CharZero K] :
    AmbientWitness K (shapePattern 1) (shapeRank 1) :=
  ambient_of_integer_minor K _ rows cols block entries
    (det_ne_zero_of_inverse_certificate block inverseNumerator 2 (by decide) inverse_check)

#print axioms shape_minor_1
end PermanentFive
