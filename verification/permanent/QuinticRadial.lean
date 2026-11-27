import QuinticKernel

/-! The coefficients of the one-variable Schur complement recover all
transfer words through degree five from the actual homogeneous polynomial. -/

noncomputable section
open PowerSeries Matrix
namespace QuinticPencil
variable {R ι σ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype σ]

private def radial (x : σ → R) : MvPolynomial σ R →+* R⟦X⟧ :=
  MvPolynomial.eval₂Hom C (fun i ↦ X * C (x i))

private theorem radial_form (l x : σ → R) : radial x (linearForm l) = X * C (value l x) := by
  simp [radial,linearForm,value,MvPolynomial.coe_eval₂Hom,map_sum,Finset.mul_sum,mul_left_comm]

set_option maxHeartbeats 800000 in
omit [Fintype σ] in
private theorem radial_hom {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) (x : σ → R) :
    radial x p = X^d * C (MvPolynomial.eval x p) := by
  calc
    radial x p = MvPolynomial.eval ((X : R⟦X⟧) • ((C : R →+* R⟦X⟧) ∘ x)) (MvPolynomial.map C p) := by
      rw [MvPolynomial.eval_map]
      simp only [Pi.smul_def,smul_eq_mul,Function.comp_def]
      rfl
    _ = _ := by rw [(hp.map (C : R →+* R⟦X⟧)).eval_smul,MvPolynomial.eval_map,← MvPolynomial.eval₂_comp]

def scalarWord (b c : ι → σ → R) (D : ι → ι → σ → R) (x : σ → R) (n : ℕ) :=
  ∑ j, ∑ i, ((transfer D x)^n) i j * (value (b i) x * value (c j) x)

private theorem radial_schur (b c : ι → σ → R) (D : ι → ι → σ → R) (x : σ → R) :
    radial x (regularDet b c D) =
      X^2 * ((lineBlock (transfer D x)).det * PowerSeries.mk (scalarWord b c D x)) := by
  let Z := transfer D x
  let T := lineBlock Z
  let B : Matrix Unit ι R⟦X⟧ := Matrix.of (fun _ i ↦ C (value (b i) x))
  let E : Matrix ι Unit R⟦X⟧ := Matrix.of (fun i _ ↦ C (value (c i) x))
  have inv : T * geometric Z = 1 := lineBlock_mul_geometric Z
  let _ : Invertible T := invertibleOfRightInverse T (geometric Z) inv
  have entry : (B * geometric Z * E) () () = PowerSeries.mk (scalarWord b c D x) := by
    ext n
    simp only [Matrix.mul_apply,B,E,geometric,Matrix.of_apply,Finset.sum_mul,map_sum,
      PowerSeries.coeff_mul_C,PowerSeries.coeff_C_mul,PowerSeries.coeff_mk,scalarWord,Z]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    radial x (regularDet b c D) =
        (Matrix.fromBlocks 0 (X • (-B)) (X • E) T).det := by
      rw [regularDet,RingHom.map_det]
      congr 1
      ext i j
      cases i <;> cases j <;>
        simp [B,E,T,Z,lineBlock,transfer,Matrix.fromBlocks,RingHom.mapMatrix_apply,radial_form,
          Matrix.one_apply]
    _ = X^2 * (Matrix.fromBlocks 0 (-B) E T).det := scale_border X (-B) E T
    _ = _ := by
      rw [Matrix.det_fromBlocks₂₂,invOf_eq_right_inv inv,Matrix.neg_mul,Matrix.neg_mul,zero_sub,
        neg_neg,Matrix.det_unique (n := Unit)]
      simpa only using congrArg (fun a ↦ X^2 * (T.det * a)) entry

/-- The zeroth, first and second words vanish and the third is the quintic. -/
theorem radial_moment {p : MvPolynomial σ R} (hp : p.IsHomogeneous 5)
    (b c : ι → σ → R) (D : ι → ι → σ → R) (rep : p = regularDet b c D)
    (x : σ → R) (j : ℕ) (hj : j ≤ 3) :
    scalarWord b c D x j = if j=3 then MvPolynomial.eval x p else 0 := by
  have product : (lineBlock (transfer D x)).det * PowerSeries.mk (scalarWord b c D x) =
      monomial 3 (MvPolynomial.eval x p) := by
    apply X_pow_mul_cancel (k := 2)
    rw [← radial_schur,← rep,radial_hom hp,monomial_eq_C_mul_X_pow]
    ring
  have unit : coeff 0 (lineBlock (transfer D x)).det = 1 :=
    (coeff_zero_eq_constantCoeff_apply _).trans (lineBlock_constant _)
  simpa only [PowerSeries.coeff_mk] using
    QuinticEndpoint.initial_moments _ _ 3 _ unit product j hj

#print axioms radial_moment
end QuinticPencil
