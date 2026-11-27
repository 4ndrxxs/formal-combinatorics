import QuinticNormalized
import QuinticDirectional

/-! The Hessian at an arbitrary centre, restricted to the common endpoint
kernel, has rank at most twice the deficit in endpoint dimension. -/

noncomputable section
open LinearMap Module
namespace QuinticPencil
variable {K ι σ : Type*} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ]
  [Fintype ι] [DecidableEq ι]

omit [CharZero K] in
private theorem rank_of_isotropic {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : LinearMap.BilinForm K V) (J : Submodule K V) (iso : J ≤ H.orthogonal J) :
    finrank K H.range + 2 * finrank K J ≤ 2 * finrank K V := by
  have a : finrank K J + finrank K (H.orthogonal J) = finrank K V + finrank K ↥(J ⊓ H.ker) :=
    H.finrank_add_finrank_orthogonal' J
  have b : finrank K J ≤ finrank K (H.orthogonal J) := Submodule.finrank_mono iso
  have c : finrank K ↥(J ⊓ H.ker) ≤ finrank K H.ker := Submodule.finrank_mono inf_le_right
  have d : finrank K H.range + finrank K H.ker = finrank K V := H.finrank_range_add_finrank_ker
  omega

theorem normalized_restricted_hessian {p : MvPolynomial σ K} (hp : p.IsHomogeneous 5)
    (b c : ι → σ → K) (D : ι → ι → σ → K) (rep : p = regularDet b c D) (y : σ → K) :
    finrank K ((hessian p y).toBilin'.restrict (endpoints b c).ker).range +
      2 * finrank K (endpoints b c).range ≤ 2 * Fintype.card ι := by
  let L := (endpoints b c).ker
  let H := (hessian p y).toBilin'.restrict L
  obtain ⟨J,dim,even⟩ := normalized_many_even hp b c D rep y
  have sym : (hessian p y).toBilin'.IsSymm := by
    apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
    ext i j
    change MvPolynomial.eval y (MvPolynomial.pderiv j (MvPolynomial.pderiv i p)) = _
    rw [MvPolynomial.pderiv_comm j i]
    rfl
  have diag (z : L) (hz : z ∈ J) : H z z = 0 := by
    apply hessian_zero_of_even p y z.val
    intro t
    exact even (t • z) (J.smul_mem t hz)
  have iso : J ≤ H.orthogonal J := by
    intro u hu v hv
    have eq := diag (u+v) (J.add_mem hu hv)
    simp only [map_add,LinearMap.add_apply,diag u hu,diag v hv,zero_add,add_zero] at eq
    have flip : H v u = H u v := sym.eq v.val u.val
    have h : 2 * H v u = 0 := by linear_combination eq + flip
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have rankBound : finrank K H.range + 2 * finrank K J ≤ 2 * finrank K L := rank_of_isotropic H J iso
  change finrank K L + finrank K (endpoints b c).range ≤ finrank K J + Fintype.card ι at dim
  change finrank K H.range + 2 * finrank K (endpoints b c).range ≤ 2 * Fintype.card ι
  omega

#print axioms normalized_restricted_hessian
end QuinticPencil
