import QuinticRegular
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Relate the formal direction coefficients to the usual symbolic partial
derivatives and the Hessian matrix in the coordinate basis. -/

noncomputable section
open PowerSeries Matrix Module
namespace QuinticPencil

variable {R S I : Type*} [CommRing R] [CommRing S] [DecidableEq I]

private def variableLine (f : R →+* S) (z v : I → S) : MvPolynomial I R →+* S⟦X⟧ :=
  MvPolynomial.eval₂Hom (C.comp f) (fun j ↦ C (z j) + X * C (v j))

omit [DecidableEq I] in
private theorem variableLine_zero (f : R →+* S) (z v : I → S) (p : MvPolynomial I R) :
    constantCoeff (variableLine f z v p) = MvPolynomial.eval₂Hom f z p := by
  unfold variableLine
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr _ _ rfl
  · apply RingHom.ext
    intro x
    simp
  · simp

private theorem variableLine_first (f : R →+* S) (z : I → S) (i : I) (p : MvPolynomial I R) :
    coeff 1 (variableLine f z (Pi.single i 1) p) =
      MvPolynomial.eval₂Hom f z (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [variableLine, MvPolynomial.coe_eval₂Hom]
  | add a b ha hb => simp [map_add,ha,hb]
  | mul_X a j ha =>
    rw [map_mul,coeff_one_mul,ha,variableLine_zero,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul]
    simp only [variableLine_zero]
    by_cases hj : j = i
    · subst j
      simp [variableLine, MvPolynomial.coe_eval₂Hom,add_comm,mul_comm]
    · simp [variableLine, MvPolynomial.coe_eval₂Hom,MvPolynomial.pderiv_X_of_ne hj,
        Pi.single_apply,hj]

theorem first_partial (p : MvPolynomial I R) (z : I → R) (i : I) :
    coeff 1 (restrictLine z (Pi.single i 1) p) =
      MvPolynomial.eval z (MvPolynomial.pderiv i p) :=
  variableLine_first (RingHom.id R) z i p

omit [DecidableEq I] in
private theorem variable_outer (p : MvPolynomial I R) (z u v : I → R) :
    atPoint p z u v =
      variableLine C (fun j ↦ C (z j) + X*C (u j)) (fun j ↦ C (v j)) p := by
  unfold atPoint variableLine
  apply MvPolynomial.eval₂Hom_congr rfl _ rfl
  funext j
  simp [directions,embed,edge,add_assoc]

/-- The mixed derivative in the coordinate directions is the value of the
two symbolic partial derivatives, including when the two directions coincide. -/
theorem mixed_partial (p : MvPolynomial I R) (z : I → R) (i j : I) :
    mixed R (atPoint p z (Pi.single i 1) (Pi.single j 1)) =
      MvPolynomial.eval z (MvPolynomial.pderiv i (MvPolynomial.pderiv j p)) := by
  have v : (fun k : I ↦ (C (R := R)) ((Pi.single j (1 : R) : I → R) k)) =
      (Pi.single j (1 : R⟦X⟧) : I → R⟦X⟧) := by
    funext k
    by_cases h : k = j <;> simp [h]
  rw [variable_outer,v]
  change coeff 1 (coeff 1 (variableLine C _ (Pi.single j 1) p)) = _
  rw [variableLine_first]
  exact first_partial _ z i


/-- Entrywise values of the usual symbolic Hessian. -/
def hessian (p : MvPolynomial I R) (z : I → R) : Matrix I I R :=
  Matrix.of fun i j ↦ MvPolynomial.eval z (MvPolynomial.pderiv i (MvPolynomial.pderiv j p))

variable {K n : Type*} [Field K] [Fintype I] [Fintype n] [DecidableEq n]

private lemma hessian_rank {p : MvPolynomial I K} {z : I → K}
    (H : LinearMap.BilinForm K (I → K)) (hH : ∀ u v, H u v = mixed K (atPoint p z u v)) :
    (hessian p z).rank = finrank K H.range := by
  let e := (dotProductEquiv K I).symm
  let A := e.toLinearMap.comp H
  have mat : A.toMatrix' = hessian p z := by
    ext i j
    change H (Pi.single j 1) (Pi.single i 1) = _
    rw [hH,mixed_partial,MvPolynomial.pderiv_comm]
    rfl
  rw [← mat,Matrix.rank,← Matrix.toLin'_apply',Matrix.toLin'_toMatrix']
  change finrank K (e.toLinearMap.comp H).range = _
  rw [LinearMap.range_comp]
  exact e.finrank_map_eq H.range

/-- A coordinate formulation of both conclusions of the regular pencil
theorem, with Mathlib's symbolic partial derivatives and matrix rank. -/
theorem regular_partial_kernel (A : Matrix n n K) (F : I → Matrix n n K)
    (regular : Fintype.card n = A.rank+1) {p : MvPolynomial I K}
    (rep : p = (affineMatrix A F).det) (hp : p.IsHomogeneous 5) :
    ∃ L : Submodule K (I → K), ∀ z ∈ L,
      (∀ i, MvPolynomial.eval z (MvPolynomial.pderiv i p) = 0) ∧
      Fintype.card I + (hessian p z).rank + 1 ≤ Fintype.card n + finrank K L := by
  obtain ⟨L,prop⟩ := regular_quintic_kernel A F regular rep hp
  refine ⟨L,fun z hz ↦ ?_⟩
  obtain ⟨sing,H,hH,rank⟩ := prop z hz
  refine ⟨fun i ↦ ?_,by rw [hessian_rank H hH]; exact rank⟩
  rw [← first_partial]
  exact X_pow_dvd_iff.mp (sing _) 1 (by decide)

#print axioms regular_partial_kernel

#print axioms first_partial
#print axioms mixed_partial
end QuinticPencil
