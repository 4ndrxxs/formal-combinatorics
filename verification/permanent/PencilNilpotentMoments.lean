import PencilHomogeneousRank
import PencilMomentEquality
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! If the internal matrix is nilpotent, the prefactor in the moment identity
is one. When the Krylov dimension bound fills the doubled space, the transfer
therefore has nilpotence index at most the degree minus one. -/

noncomputable section
open Matrix Module LinearMap PowerSeries PencilMoment
namespace QuinticPencil
variable {K I n : Type*} [Field K] [Fintype n] [DecidableEq n] [Fintype I] [DecidableEq I]

theorem lineBlock_det_one_of_nilpotent (A : Matrix n n K) (nil : IsNilpotent A) :
    (lineBlock A).det = 1 := by
  obtain ⟨r,_,eq⟩ := Polynomial.isUnit_iff.mp (Matrix.isUnit_charpolyRev_of_isNilpotent nil)
  have one : r = 1 := by simpa [← eq] using A.eval_charpolyRev
  have rev : A.charpolyRev = 1 := by rw [←eq,one,Polynomial.C_1]
  let f := Polynomial.coeToPowerSeries.ringHom (R:=K)
  have e : f.mapMatrix (1 - (Polynomial.X : Polynomial K) • A.map Polynomial.C) = lineBlock A := by
    ext i j
    simp [f,lineBlock,Matrix.one_apply,apply_ite,RingHom.mapMatrix_apply,
      Polynomial.coeToPowerSeries.ringHom_apply]
    exact mul_comm _ _
  have val := congrArg f rev
  change f ((1 - (Polynomial.X : Polynomial K) • A.map Polynomial.C).det) = f 1 at val
  rwa [RingHom.map_det,e,map_one] at val

omit [DecidableEq I] in
theorem transfer_tail_zero {p : MvPolynomial I K} {s : ℕ} (hp : p.IsHomogeneous (s+2))
    (b c : n → I → K) (D : n → n → I → K) (rep : p = regularDet b c D)
    (z : I → K) (hz : z ∈ (endpoints b c).ker) (nil : IsNilpotent (transfer D z))
    (j : ℕ) (after : s < j) (x y : I → K) :
    dualProd K (n → K) (endpoints b c x)
      (((doubledTransfer (transfer D z))^j) (endpoints b c y)) = 0 := by
  let P := endpoints b c
  let M := doubledTransfer (transfer D z)
  let B := dualProd K (n → K)
  obtain ⟨hb,hc⟩ := (endpoint_zero_iff b c z).mp hz
  have ser : (lineBlock (transfer D z)).det *
      PowerSeries.mk (fun i ↦ B (P x) ((M^i) (P y))) = monomial s (mixed K (atPoint p z x y)) := by
    simpa only [P,M,B,doubledTransfer_moment] using affine_pencil_series hp b c D rep z x y hb hc
  rw [lineBlock_det_one_of_nilpotent _ nil,one_mul] at ser
  have coef := congrArg (PowerSeries.coeff j) ser
  simpa only [PowerSeries.coeff_mk,PowerSeries.coeff_monomial,ite_eq_right after.ne'] using coef

/-- If the endpoint and moment ranks already account for the entire
doubled space through order s, the internal matrix has (s+1)st power zero. -/
theorem transfer_power_of_full_rank {p : MvPolynomial I K} {s : ℕ} (hp : p.IsHomogeneous (s+2))
    (b c : n → I → K) (D : n → n → I → K) (rep : p = regularDet b c D)
    (z : I → K) (hz : z ∈ (endpoints b c).ker) (nil : IsNilpotent (transfer D z))
    (large : 2 * Fintype.card n ≤ finrank K (endpoints b c).range + s * (hessian p z).rank) :
    (transfer D z)^(s+1) = 0 := by
  let A := transfer D z
  let P := endpoints b c
  let M := doubledTransfer A
  let B := dualProd K (n → K)
  obtain ⟨H,actual,values⟩ := homogeneous_kernel_moments hp b c D rep z hz
  have zero (j : ℕ) (hj : j<s) (x y : I → K) : B (P x) ((M^j) (P y)) = 0 := by
    simpa only [ite_eq_right hj.ne] using values j hj.le x y
  have moment (x y : I → K) : B (P x) ((M^s) (P y)) = H x y := by
    simpa only [ite_true] using values s (Nat.le_refl _) x y
  have bound := flag_dimension B P M (doubledTransfer_adjoint _) s H zero moment s (Nat.le_refl _)
  rw [hessian_rank_from_mixed H actual] at large
  have ambient : finrank K (Ends K n) = 2*Fintype.card n := by
    simp [Ends,Module.finrank_prod,Subspace.dual_finrank_eq,two_mul]
  have full : flag P M s = ⊤ := Submodule.eq_top_of_finrank_eq
    (le_antisymm (flag P M s).finrank_le (ambient ▸ large.trans bound))
  have stop := power_zero_of_full_flag B dualProd_nondegenerate P M (doubledTransfer_adjoint _)
    s full (transfer_tail_zero hp b c D rep z hz nil)
  have linear : (A^(s+1)).toLin' = 0 := by
    apply LinearMap.ext
    intro x
    have hit := LinearMap.congr_fun stop ((0,x) : Ends K n)
    rw [show M = doubledTransfer A from rfl,doubledTransfer_pow] at hit
    exact congrArg Prod.snd hit
  exact Matrix.toLin'.injective (by simpa using linear)

#print axioms lineBlock_det_one_of_nilpotent
#print axioms transfer_power_of_full_rank
end QuinticPencil
