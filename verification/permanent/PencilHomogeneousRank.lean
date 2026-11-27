import PencilMomentFlag
import QuinticDerivatives
import QuinticPivotExtension

/-! Endpoint dimension and Hessian rank in every homogeneous degree at least
three. The coefficient of the rank is degree minus three. -/

noncomputable section
open Matrix Module LinearMap PowerSeries PencilMoment
namespace QuinticPencil
variable {K I n : Type*} [Field K] [Fintype n] [DecidableEq n] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- In degree s+2 the first s transfer moments vanish and the next equals
the mixed second derivative. -/
theorem homogeneous_kernel_moments {p : MvPolynomial I K} {s : ℕ}
    (hp : p.IsHomogeneous (s+2)) (b c : n → I → K) (D : n → n → I → K)
    (rep : p = regularDet b c D) (z : I → K) (hz : z ∈ (endpoints b c).ker) :
    ∃ H : (I → K) →ₗ[K] Dual K (I → K),
      (∀ x y, H x y = mixed K (atPoint p z x y)) ∧
      ∀ j ≤ s, ∀ x y, dualProd K (n → K) (endpoints b c x)
        (((doubledTransfer (transfer D z))^j) (endpoints b c y)) = if j=s then H x y else 0 := by
  let B := dualProd K (n → K)
  let P := endpoints b c
  let M := doubledTransfer (transfer D z)
  let H := QuinticEndpoint.pair B P (layer P M s)
  obtain ⟨hb,hc⟩ := (endpoint_zero_iff b c z).mp hz
  have unit : coeff 0 (lineBlock (transfer D z)).det = 1 :=
    (coeff_zero_eq_constantCoeff_apply _).trans (lineBlock_constant _)
  have eq (x y : I → K) (j : ℕ) (hj : j ≤ s) :
      B (P x) ((M^j) (P y)) = if j=s then mixed K (atPoint p z x y) else 0 := by
    have ser : (lineBlock (transfer D z)).det *
        PowerSeries.mk (fun i ↦ B (P x) ((M^i) (P y))) =
        monomial s (mixed K (atPoint p z x y)) := by
      simpa only [B,P,M,doubledTransfer_moment] using
        affine_pencil_series hp b c D rep z x y hb hc
    simpa only [PowerSeries.coeff_mk] using QuinticEndpoint.initial_moments _ _ s _ unit ser j hj
  have hH (x y : I → K) : H x y = mixed K (atPoint p z x y) := by
    simpa [H,QuinticEndpoint.pair,layer] using eq x y s (by omega)
  exact ⟨H,hH,fun j hj x y ↦ by rw [hH]; exact eq x y j hj⟩

/-- If d=s+3, then 2 rank(Phi) + (d-3) rank(Hess_z) is at most
twice the size of the internal block. -/
theorem homogeneous_endpoint_rank {p : MvPolynomial I K} {s : ℕ}
    (hp : p.IsHomogeneous (s+3)) (b c : n → I → K) (D : n → n → I → K)
    (rep : p = regularDet b c D) (z : I → K) (hz : z ∈ (endpoints b c).ker) :
    2 * finrank K (endpoints b c).range + s * (hessian p z).rank ≤ 2 * Fintype.card n := by
  let P := endpoints b c
  let M := doubledTransfer (transfer D z)
  let B := dualProd K (n → K)
  obtain ⟨H,actual,values⟩ := homogeneous_kernel_moments (s:=s+1) hp b c D rep z hz
  have zero (j : ℕ) (hj : j<s+1) (x y : I → K) : B (P x) ((M^j) (P y)) = 0 := by
    simpa only [ite_eq_right hj.ne] using values j hj.le x y
  have moment (x y : I → K) : B (P x) ((M^(s+1)) (P y)) = H x y := by
    simpa only [ite_true] using values (s+1) (Nat.le_refl _) x y
  have bound := PencilMoment.endpoint_dimension B dualProd_nondegenerate P M
    (doubledTransfer_adjoint _) s H zero moment
  rw [hessian_rank_from_mixed H actual]
  simpa only [Module.finrank_prod,Subspace.dual_finrank_eq,Module.finrank_pi,two_mul] using bound

/-- Coordinate version for a regular affine expression. -/
theorem regular_homogeneous_rank {p : MvPolynomial I K} {s : ℕ}
    (hp : p.IsHomogeneous (s+3)) (A : Matrix n n K) (F : I → Matrix n n K)
    (regular : Fintype.card n = A.rank+1) (rep : p = (affineMatrix A F).det) :
    ∃ L : Submodule K (I → K), ∀ z ∈ L, 2*Fintype.card I + s*(hessian p z).rank ≤
      2*(A.rank + finrank K L) := by
  obtain ⟨b,c,D,norm⟩ := normalize_regular A F regular rep (d:=s+1) hp
  refine ⟨(endpoints b c).ker,fun z hz ↦ ?_⟩
  have bnd := homogeneous_endpoint_rank hp b c D norm z hz
  rw [Fintype.card_fin] at bnd
  have dim := (endpoints b c).finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at dim
  omega

#print axioms homogeneous_kernel_moments
#print axioms homogeneous_endpoint_rank
#print axioms regular_homogeneous_rank
end QuinticPencil
