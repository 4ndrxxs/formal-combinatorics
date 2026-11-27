import PermanentRectangleEntries

/-! Duplicating the fourth column at the auxiliary row gives the same Gram matrix on
any choices of one of the two copies in each of the first three rows. -/

noncomputable section
open Matrix QuinticPencil
namespace PermanentFive.Rectangle

def extendedCentre (e : Cell) : Token := if e = (3,3) then (1,0,0) else centreCode e

def extendedDirections : Fin 15 → Cell :=
  ![(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)]

def merge : Fin 15 → Fin 12 := ![0,1,2,3,3,4,5,6,7,7,8,9,10,11,11]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 36000000 in
private theorem degree_one (i j : Fin 15) : ∀ p, affineTag (termToken extendedCentre
    (extendedDirections i) (extendedDirections j) p) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 48000000 in
private theorem coefficients_agree (i j : Fin 15) :
    let a := blockCoefficient extendedCentre (extendedDirections i) (extendedDirections j)
    let b := blockCoefficient centreCode (directions (merge i)) (directions (merge j))
    a (0,0) = b (0,0) ∧ a (1,0) = b (1,0) ∧ a (0,1) = b (0,1) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem duplicated_hessian {R : Type*} [CommRing R] (s t : R) :
    (hessian (per R Idx) (value s t ∘ extendedCentre)).submatrix extendedDirections extendedDirections =
      (original s t).submatrix merge merge := by
  rw [← hessian_original]
  ext1 i j
  simp only [Matrix.submatrix_apply,second_formula]
  rw [affine_second s t _ _ _ (degree_one i j),
    affine_second s t _ _ _ (rectangle_terms_affine (merge i) (merge j))]
  obtain ⟨h₀,h₁,h₂⟩ := coefficients_agree i j
  rw [h₀,h₁,h₂]

#print axioms duplicated_hessian
end PermanentFive.Rectangle
