import QuinticRadial
import QuinticSaturation

/-! Endpoints of a normalized quintic pencil and its transfer endomorphisms
satisfy the polarized cancellation when their range is maximal isotropic. -/

noncomputable section
open Matrix Module LinearMap
namespace QuinticPencil
variable {K ι σ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype σ]

private def leftEnd (b : ι → σ → K) : (σ → K) →ₗ[K] Dual K (ι → K) :=
  ((dotProductEquiv K ι).toLinearMap).comp (Matrix.of b).mulVecLin

private def rightEnd (c : ι → σ → K) : (σ → K) →ₗ[K] (ι → K) := (Matrix.of c).mulVecLin

private def transferLinear (D : ι → ι → σ → K) : (σ → K) →ₗ[K] Matrix ι ι K where
  toFun := transfer D
  map_add' x y := by ext i j; simp [transfer,value,mul_add,Finset.sum_add_distrib]
  map_smul' a y := by ext i j; simp [transfer,value,Finset.mul_sum,mul_left_comm]

private def operator (D : ι → ι → σ → K) : (σ → K) →ₗ[K] End K (ι → K) :=
  Matrix.toLin'.toLinearMap.comp (transferLinear D)

private theorem operator_power (D : ι → ι → σ → K) (x : σ → K) (j : ℕ) :
    ((operator D x)^j) = ((transfer D x)^j).toLin' := by
  induction j with
  | zero => simp; rfl
  | succ j ih => rw [pow_succ,pow_succ,Matrix.toLin'_mul,ih]; rfl

private theorem word_action (b c : ι → σ → K) (D : ι → ι → σ → K) (x : σ → K) (j : ℕ) :
    scalarWord b c D x j = leftEnd b x (((operator D x)^j) (rightEnd c x)) := by
  rw [operator_power]
  change (∑ l, ∑ i, ((transfer D x)^j) i l * (value (b i) x * value (c l) x)) =
    ∑ i, value (b i) x * ∑ l, ((transfer D x)^j) i l * value (c l) x
  rw [Finset.sum_comm]
  simp [Finset.mul_sum,mul_left_comm]

/-- The determinant itself has zero even second difference along its common
endpoint kernel whenever the endpoint range has half the ambient dimension. -/
theorem normalized_even_difference [CharZero K] {p : MvPolynomial σ K} (hp : p.IsHomogeneous 5)
    (b c : ι → σ → K) (D : ι → ι → σ → K) (rep : p = regularDet b c D)
    (full : finrank K (endpoints b c).range = Fintype.card ι)
    (z : σ → K) (hz : z ∈ (endpoints b c).ker) (y : σ → K) :
    MvPolynomial.eval (y+z) p + MvPolynomial.eval (y-z) p = 2 * MvPolynomial.eval y p := by
  let B := leftEnd b
  let C := rightEnd c
  let A := operator D
  have words (x : σ → K) (n : ℕ) (hn : n ≤ 3) :
      B x (((A x)^n) (C x)) = if n=3 then MvPolynomial.eval x p else 0 := by
    rw [← word_action]
    exact radial_moment hp b c D rep x n hn
  have q (x : σ → K) : B x (C x) = 0 := by simpa using words x 0 (by decide)
  have cu (x : σ → K) : B x (A x (C x)) = 0 := by simpa using words x 1 (by decide)
  have qu (x : σ → K) : B x (A x (A x (C x))) = 0 := by
    simpa [pow_succ] using words x 2 (by decide)
  have p5 (x : σ → K) : MvPolynomial.eval x p = B x (A x (A x (A x (C x)))) := by
    simpa [pow_succ] using (words x 3 (by decide)).symm
  have hP : endpoints b c z = 0 := hz
  have bz : B z = 0 := congrArg Prod.fst hP
  have cz : C z = 0 := congrArg Prod.snd hP
  have range : finrank K (B.prod C).range = finrank K (ι → K) := full.trans (Module.finrank_pi K).symm
  exact QuinticSaturation.even_difference B C A cu qu _ p5 z bz cz
    (QuinticSaturation.lift_of_half_dimension B C A q cu range z bz cz) y

#print axioms normalized_even_difference
end QuinticPencil
