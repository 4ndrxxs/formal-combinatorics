import QuinticRestricted

/-! In ambient coordinates the space of simultaneously isotropic
directions has dimension at least the input dimension minus the size of
the invertible block, at each centre over the field of definition. -/

noncomputable section
open Module LinearMap Matrix
namespace QuinticPencil
variable {K I n : Type*} [Field K] [CharZero K] [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n]

theorem normalized_isotropic_directions {p : MvPolynomial I K} (hp : p.IsHomogeneous 5)
    (b c : n → I → K) (D : n → n → I → K) (rep : p = regularDet b c D) (y : I → K) :
    ∃ J : Submodule K (I → K), J ≤ (endpoints b c).ker ∧
      Fintype.card I ≤ finrank K J + Fintype.card n ∧ J ≤ (hessian p y).toBilin'.orthogonal J := by
  let L := (endpoints b c).ker
  let H := (hessian p y).toBilin'
  obtain ⟨J,dim,even⟩ := normalized_many_even hp b c D rep y
  let A := J.map L.subtype
  have dims : finrank K J = finrank K A := (Submodule.equivMapOfInjective L.subtype L.subtype_injective J).finrank_eq
  have total := (endpoints b c).finrank_range_add_finrank_ker.trans (Module.finrank_pi K)
  refine ⟨A,L.map_subtype_le J,by omega,?_⟩
  have diag (z : I → K) (hz : z ∈ A) : H z z = 0 := by
    obtain ⟨v,hv,rfl⟩ := hz
    apply hessian_zero_of_even p y v.val
    intro t
    exact even (t • v) (J.smul_mem t hv)
  have sym : H.IsSymm := by
    apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
    ext i j
    change MvPolynomial.eval y (MvPolynomial.pderiv j (MvPolynomial.pderiv i p)) = _
    rw [MvPolynomial.pderiv_comm j i]
    rfl
  intro u hu v hv
  have e := diag (u+v) (A.add_mem hu hv)
  simp only [map_add,LinearMap.add_apply,diag u hu,diag v hv,zero_add,add_zero] at e
  have pair : 2 * H v u = 0 := by linear_combination e + sym.eq v u
  exact (mul_eq_zero.mp pair).resolve_left (by norm_num)

#print axioms normalized_isotropic_directions
end QuinticPencil
