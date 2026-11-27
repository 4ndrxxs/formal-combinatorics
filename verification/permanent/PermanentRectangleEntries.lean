import PermanentRectangleTokens

/-! The entries of the three-by-four Hessian block at the two-parameter centre. -/

open Matrix QuinticPencil
namespace PermanentFive.Rectangle
abbrev Mat (R : Type*) := Matrix (Fin 12) (Fin 12) R
def directions : Fin 12 → Cell := ![(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,3), (2,0), (2,1), (2,2), (2,3)]
def centreCode (e : Cell) : Token :=
  (![![(1,1,0), (-1,1,0), (1,0,0), (1,0,0), (0,0,0)],
     ![(1,0,1), (1,0,0), (-1,0,1), (1,0,0), (0,0,0)],
     ![(1,0,0), (1,0,0), (1,0,0), (3,0,0), (0,0,0)],
     ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (1,0,0)],
     ![(1,0,0), (1,0,0), (1,0,0), (-1,0,0), (0,0,0)]] : Idx → Idx → Token) e.1 e.2

def original {R : Type*} [CommRing R] (s t : R) : Mat R :=
  Matrix.of ![![0, 0, 0, 0, 0, 2, 2, 2, 0, 1 + t, 0, 1 - t],
     ![0, 0, 0, 0, 2, 0, 2, 2, 1 + t, 0, 1 - t, 0],
     ![0, 0, 0, 0, 2, 2, 0, 2, 0, 1 - t, 0, 1 + t],
     ![0, 0, 0, 0, 2, 2, 2, 0, 1 - t, 0, 1 + t, 0],
     ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1 + s, 1 - s],
     ![2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1 - s, 1 + s],
     ![2, 2, 0, 2, 0, 0, 0, 0, 1 + s, 1 - s, 0, 0],
     ![2, 2, 2, 0, 0, 0, 0, 0, 1 - s, 1 + s, 0, 0],
     ![0, 1 + t, 0, 1 - t, 0, 0, 1 + s, 1 - s, 0, 0, 0, 0],
     ![1 + t, 0, 1 - t, 0, 0, 0, 1 - s, 1 + s, 0, 0, 0, 0],
     ![0, 1 - t, 0, 1 + t, 1 + s, 1 - s, 0, 0, 0, 0, 0, 0],
     ![1 - t, 0, 1 + t, 0, 1 - s, 1 + s, 0, 0, 0, 0, 0, 0]]

private def constantCoeff : Mat ℤ :=
  Matrix.of ![![0, 0, 0, 0, 0, 2, 2, 2, 0, 1, 0, 1],
     ![0, 0, 0, 0, 2, 0, 2, 2, 1, 0, 1, 0],
     ![0, 0, 0, 0, 2, 2, 0, 2, 0, 1, 0, 1],
     ![0, 0, 0, 0, 2, 2, 2, 0, 1, 0, 1, 0],
     ![0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1],
     ![2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 1],
     ![2, 2, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0],
     ![2, 2, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0],
     ![0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0],
     ![1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0],
     ![0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0],
     ![1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0]]

private def sCoeff : Mat ℤ :=
  Matrix.of ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1],
     ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
     ![0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
     ![0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0],
     ![0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0]]

private def tCoeff : Mat ℤ :=
  Matrix.of ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1],
     ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0],
     ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1],
     ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0],
     ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
     ![1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     ![0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
     ![-1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 24000000 in
theorem rectangle_terms_affine (i j : Fin 12) : ∀ p, affineTag (termToken centreCode (directions i) (directions j) p) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 24000000 in
private theorem coeffs (i j : Fin 12) :
    blockCoefficient centreCode (directions i) (directions j) (0,0) = constantCoeff i j ∧
    blockCoefficient centreCode (directions i) (directions j) (1,0) = sCoeff i j ∧
    blockCoefficient centreCode (directions i) (directions j) (0,1) = tCoeff i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem hessian_original {R : Type*} [CommRing R] (s t : R) :
    (hessian (per R Idx) (value s t ∘ centreCode)).submatrix directions directions = original s t := by
  ext i j
  change hessian _ _ (directions i) (directions j) = _
  rw [second_formula,affine_second s t _ _ _ (rectangle_terms_affine i j)]
  obtain ⟨h₀,h₁,h₂⟩ := coeffs i j
  rw [h₀,h₁,h₂]
  fin_cases i <;> fin_cases j <;> norm_num [original,constantCoeff,sCoeff,tCoeff] <;> ring

#print axioms hessian_original
end PermanentFive.Rectangle
