import DeterminantalParametrization

/-! The first-order determinant vanishes identically at the parametrized
matrix of corank at least two. Replacing one column increases the inner
dimension of the factorization by at most one. -/
noncomputable section
namespace DeterminantalRegularity
open Matrix Finset

theorem update_factor_det_zero {R H I : Type*} [CommRing R] [IsDomain R]
    [Fintype H] [Fintype I] [DecidableEq I] (B : Matrix I H R) (D : Matrix H I R)
    (c : I) (v : I → R) (room : Fintype.card H + 1 < Fintype.card I) :
    ((B*D).updateCol c v).det = 0 := by
  let P : Matrix I (H ⊕ Unit) R := Matrix.of (fun i ↦ Sum.elim (B i) (fun _ ↦ v i))
  let Q : Matrix (H ⊕ Unit) I R := Matrix.of (fun h j ↦ Sum.elim
    (fun k ↦ if j = c then 0 else D k j) (fun _ ↦ if j = c then 1 else 0) h)
  have fac : P*Q = (B*D).updateCol c v := by
    ext i j
    by_cases h : j = c <;> simp [P,Q,Matrix.mul_apply,Fintype.sum_sum_type,h]
  rw [← fac]
  by_contra nz
  have bound := (Matrix.rank_mul_le_left P Q).trans (Matrix.rank_le_card_width P)
  rw [Matrix.rank_of_det_ne_zero nz] at bound
  simp at bound
  omega

namespace RankParam
open MvPolynomial
variable (K : Type*) [Field K] (U H : Type*) [Fintype H] [DecidableEq H]

private def basisCols : Matrix (Slot H) H (Poly K U H) :=
  Matrix.of (fun r k ↦ Sum.elim (fun i ↦ if i = k then 1 else 0) (fun b ↦ coeffRows K U H b k) r)

private theorem raw_product : basisCols K U H * topRows K U H = raw K U H := by
  apply Matrix.ext
  intro r j
  cases r with
  | inl i => simp [basisCols,raw,Matrix.mul_apply,ite_mul]
  | inr b => rfl

/-- Each of the column replacements in the determinant derivative is
already zero in the coordinate ring. -/
theorem column_zero (c : Slot H) (v : Slot H → Coord K U H) :
    ((entry K U H).updateCol c v).det = 0 := by
  apply Subtype.val_injective
  change incl K U H ((entry K U H).updateCol c v).det = incl K U H 0
  have eq : (incl K U H).mapMatrix ((entry K U H).updateCol c v) =
      (raw K U H).updateCol c (fun i ↦ incl K U H (v i)) := by
    ext i j
    by_cases h : j = c <;> simp [h]
  rw [RingHom.map_det,eq,← raw_product,map_zero]
  apply update_factor_det_zero
  simp [Slot]

#print axioms column_zero
end RankParam
end DeterminantalRegularity
