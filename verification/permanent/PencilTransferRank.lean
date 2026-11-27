import PencilHomogeneousRank
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! The leading nonzero moment factors the Hessian through the corresponding
power of the internal transfer. This gives an additional bound at every
point of the common endpoint kernel, in every homogeneous degree. -/

noncomputable section
open Matrix Module LinearMap
namespace QuinticPencil
variable {K I n : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n]

set_option backward.isDefEq.respectTransparency false in
theorem doubled_power_rank (A : Matrix n n K) (s : ℕ) :
    finrank K ((doubledTransfer A)^s).range = 2 * (A^s).rank := by
  have eq : (doubledTransfer A)^s = doubledTransfer (A^s) := by
    apply LinearMap.ext
    intro p
    exact doubledTransfer_pow A s p
  classical
  let _ : Module.Free K (A^s).toLin'.dualMap.range := Module.Free.of_divisionRing K (A^s).toLin'.dualMap.range
  let _ : Module.Free K (A^s).toLin'.range := Module.Free.of_divisionRing K (A^s).toLin'.range
  rw [eq,doubledTransfer,LinearMap.range_prodMap,(Submodule.prodEquiv _ _).finrank_eq,
    Module.finrank_prod,LinearMap.finrank_range_dualMap_eq_finrank_range,two_mul]
  rfl

theorem hessian_rank_le_transfer_power {p : MvPolynomial I K} {s : ℕ}
    (hp : p.IsHomogeneous (s+2)) (b c : n → I → K) (D : n → n → I → K)
    (rep : p = regularDet b c D) (z : I → K) (hz : z ∈ (endpoints b c).ker) :
    (hessian p z).rank ≤ 2*((transfer D z)^s).rank := by
  let P := endpoints b c
  let M := doubledTransfer (transfer D z)
  let B := dualProd K (n → K)
  let T := P.dualMap.comp B
  obtain ⟨H,actual,values⟩ := homogeneous_kernel_moments hp b c D rep z hz
  have fact : H = T.comp ((M^s).comp P) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change H x y = B ((M^s) (P x)) (P y)
    have sl := PencilMoment.slide B M (doubledTransfer_adjoint _) (P x) (P y) s 0
    have hit := values s (Nat.le_refl _) x y
    rw [pow_zero,one_apply_eq_self,Nat.add_zero] at sl
    have last : B (P x) ((M^s) (P y)) = H x y := by simpa only [ite_true] using hit
    exact (sl.trans last).symm
  rw [hessian_rank_from_mixed H actual,fact,LinearMap.range_comp]
  have lo := Submodule.finrank_map_le T ((M^s).comp P).range
  have hi := Submodule.finrank_mono (LinearMap.range_comp_le_range P (M^s))
  exact lo.trans (hi.trans_eq (doubled_power_rank _ _))

#print axioms doubled_power_rank
#print axioms hessian_rank_le_transfer_power
end QuinticPencil
