import QuinticAffine
import QuinticEndpoint
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.LinearAlgebra.Matrix.Dual

/-! A rank bound for the actual mixed second derivative of a homogeneous
quintic given as a normalized affine determinant. -/

noncomputable section
open PowerSeries Matrix Module LinearMap
namespace QuinticPencil

variable {K ι σ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype σ]

abbrev Ends (K ι : Type*) [Field K] := Module.Dual K (ι → K) × (ι → K)

/-- Pair the row and column coefficients of the bordered determinant. -/
def endpoints (b c : ι → σ → K) : (σ → K) →ₗ[K] Ends K ι :=
  (((dotProductEquiv K ι).toLinearMap).comp (Matrix.of b).mulVecLin).prod (Matrix.of c).mulVecLin

/-- Paired action of the internal matrix on the dual and primal channels. -/
def doubledTransfer (D : Matrix ι ι K) : Ends K ι →ₗ[K] Ends K ι :=
  D.toLin'.dualMap.prodMap D.toLin'

theorem doubledTransfer_pow (D : Matrix ι ι K) (j : ℕ) (p : Ends K ι) :
    ((doubledTransfer D)^j) p = (p.1.comp ((D^j).toLin'), ((D^j).toLin') p.2) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ' (doubledTransfer D), mul_apply_eq_comp, ih]
    apply Prod.ext
    · apply LinearMap.ext
      intro y
      change p.1 (((D^j).toLin') (D.toLin' y)) = p.1 (((D^(j+1)).toLin') y)
      rw [pow_succ D, Matrix.toLin'_mul]
      rfl
    · change D.toLin' (((D^j).toLin') p.2) = ((D^(j+1)).toLin') p.2
      rw [pow_succ' D, Matrix.toLin'_mul]
      rfl

theorem doubledTransfer_adjoint (D : Matrix ι ι K) (p q : Ends K ι) :
    dualProd K (ι → K) (doubledTransfer D p) q = dualProd K (ι → K) p (doubledTransfer D q) := rfl

omit [DecidableEq ι] in
theorem dualProd_nondegenerate : (dualProd K (ι → K)).Nondegenerate := by
  apply (isSymm_dualProd K (ι → K)).isRefl.nondegenerate_iff_separatingLeft.mpr
  exact (separatingLeft_dualProd K (ι → K)).mpr (Module.eval_apply_injective K)

private lemma evaluate_row (D : Matrix ι ι K) (p q : ι → K) :
    (dotProductEquiv K ι p) (D.toLin' q) =
      ∑ l, ∑ i, D i l * (p i * q l) := by
  change (∑ i, p i * ∑ l, D i l * q l) = _
  rw [Finset.sum_comm]
  simp [Finset.mul_sum, mul_left_comm]

theorem doubledTransfer_moment (D : Matrix ι ι K) (b c : ι → σ → K) (u v : σ → K) (j : ℕ) :
    dualProd K (ι → K) (endpoints b c u) (((doubledTransfer D)^j) (endpoints b c v)) =
      ∑ l, ∑ i, (D^j) i l *
        (value (b i) u * value (c l) v + value (b i) v * value (c l) u) := by
  rw [doubledTransfer_pow, dualProd_apply_apply]
  change (dotProductEquiv K ι (fun i ↦ value (b i) v))
      ((D^j).toLin' (fun i ↦ value (c i) u)) +
    (dotProductEquiv K ι (fun i ↦ value (b i) u))
      ((D^j).toLin' (fun i ↦ value (c i) v)) = _
  rw [evaluate_row, evaluate_row]
  simp only [mul_add, Finset.sum_add_distrib]
  exact add_comm _ _

/-- The Hessian is specified by its coefficient of the two independent
direction variables. For every point of the common endpoint kernel, its
rank plus the codimension of that kernel is at most the lower block size. -/
theorem quintic_rank {p : MvPolynomial σ K} (hp : p.IsHomogeneous 5)
    (b c : ι → σ → K) (D : ι → ι → σ → K) (rep : p = regularDet b c D)
    (z : σ → K) (hz : z ∈ (endpoints b c).ker) :
    ∃ H : LinearMap.BilinForm K (σ → K),
      (∀ u v, H u v = mixed K (atPoint p z u v)) ∧
      Fintype.card σ + finrank K H.range ≤ Fintype.card ι + finrank K (endpoints b c).ker := by
  let P := endpoints b c
  let M := doubledTransfer (transfer D z)
  let B := dualProd K (ι → K)
  let H := QuinticEndpoint.pair B P (M.comp (M.comp (M.comp P)))
  have hP : P z = 0 := hz
  have hb (i : ι) : value (b i) z = 0 := by
    have hb' : dotProductEquiv K ι ((Matrix.of b).mulVecLin z) = 0 := congrArg Prod.fst hP
    have hn : (Matrix.of b).mulVecLin z = 0 := (dotProductEquiv K ι).map_eq_zero_iff.mp hb'
    exact congrFun hn i
  have hc (i : ι) : value (c i) z = 0 := congrFun (congrArg Prod.snd hP) i
  have series (u v : σ → K) : (lineBlock (transfer D z)).det *
      PowerSeries.mk (fun j ↦ B (P u) ((M^j) (P v))) =
      monomial 3 (mixed K (atPoint p z u v)) := by
    simpa only [B, P, M, doubledTransfer_moment] using
      (affine_pencil_series (d := 3) hp b c D rep z u v hb hc)
  have unit : coeff 0 (lineBlock (transfer D z)).det = 1 :=
    (coeff_zero_eq_constantCoeff_apply _).trans (lineBlock_constant _)
  have actual (u v : σ → K) : H u v = mixed K (atPoint p z u v) := by
    have e := QuinticEndpoint.initial_moments _ _ 3 _ unit (series u v) 3 (le_refl _)
    simpa [H, QuinticEndpoint.pair, pow_succ] using e
  refine ⟨H,actual,?_⟩
  have dim := QuinticEndpoint.series_rank B dualProd_nondegenerate P M (doubledTransfer_adjoint _)
    H _ unit (fun u v ↦ by rw [actual]; exact series u v)
  have kernel : finrank K P.range + finrank K P.ker = Fintype.card σ :=
    P.finrank_range_add_finrank_ker.trans (Module.finrank_pi K)
  simp only [Module.finrank_prod, Subspace.dual_finrank_eq, Module.finrank_pi] at dim
  change Fintype.card σ + finrank K H.range ≤ Fintype.card ι + finrank K P.ker
  have half : finrank K P.range + finrank K H.range ≤ Fintype.card ι :=
    Nat.le_of_mul_le_mul_left (by simpa only [two_mul] using dim) (by decide : 0 < 2)
  rw [← kernel, Nat.add_right_comm]
  exact Nat.add_le_add_right half _

#print axioms quintic_rank
end QuinticPencil
