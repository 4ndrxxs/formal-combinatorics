import PermanentAmbientEight

/-! An eight-by-eight nonsingular ambient minor at the indicator of a thirteen-cell board. -/

namespace PermanentFive
open Matrix QuinticPencil
private def rows : Fin 8 → Cell := ![(4,1), (4,0), (4,2), (4,3), (4,4), (3,1), (3,0), (3,2)]
private def cols : Fin 8 → Cell := ![(3,0), (3,1), (3,2), (3,3), (3,4), (4,0), (4,1), (4,2)]
private def block : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of ![
    ![6, 0, 4, 4, 4, 0, 0, 0],
    ![0, 6, 4, 4, 4, 0, 0, 0],
    ![4, 4, 0, 2, 2, 0, 0, 0],
    ![4, 4, 2, 0, 2, 0, 0, 0],
    ![4, 4, 2, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 6, 0, 4],
    ![0, 0, 0, 0, 0, 0, 6, 4],
    ![0, 0, 0, 0, 0, 4, 4, 0]]
private def inverseNumerator : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of ![
    ![8, -16, 8, 8, 8, 0, 0, 0],
    ![-16, 8, 8, 8, 8, 0, 0, 0],
    ![8, 8, -52, 20, 20, 0, 0, 0],
    ![8, 8, 20, -52, 20, 0, 0, 0],
    ![8, 8, 20, 20, -52, 0, 0, 0],
    ![0, 0, 0, 0, 0, 12, -12, 18],
    ![0, 0, 0, 0, 0, -12, 12, 18],
    ![0, 0, 0, 0, 0, 18, 18, -27]]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem entries : ∀ i j : Fin 8,
    secondAt (boardPoint (thirteenShape 0)) (rows i) (cols j) = block i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
private theorem inverse_check : block * inverseNumerator = (144 : ℤ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem thirteen_ambient_0 (K : Type*) [Field K] [CharZero K] : HasAmbientEight K (thirteenShape 0) :=
  ambient_eight_of_integers K _ rows cols block entries
    (det_ne_zero_of_inverse_certificate block inverseNumerator 144 (by decide) inverse_check)

#print axioms thirteen_ambient_0
end PermanentFive
