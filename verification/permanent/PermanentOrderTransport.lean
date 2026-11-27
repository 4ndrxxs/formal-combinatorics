import PermanentRankCertificate

/-! Changing both index sets by the same bijection transports the
permanent, its first partials, and its Hessian. -/
noncomputable section
open Matrix Module Equiv Finset MvPolynomial PermanentFive QuinticPencil
namespace PermanentBorder
variable {K I J : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Field K] in
private theorem unmap {A B : Type*} (x : A → K) (e : A ≃ B) : (x ∘ e.symm) ∘ e=x :=
  funext fun i ↦ congrArg x (e.symm_apply_apply i)

theorem rename_permanent (e : I ≃ J) : rename (e.prodCongr e) (per K I)=per K J := by
  simp only [per,Matrix.permanent,map_sum,map_prod,PermanentCuts.generic,Matrix.of_apply,rename_X]
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro p
  apply Fintype.prod_equiv e
  intro j
  simp [Equiv.permCongr_apply]

theorem transport_value (e : I ≃ J) (z : CellOf I → K) :
    value (z ∘ (e.prodCongr e).symm) = value z := by
  rw [value,←rename_permanent e,eval_rename]
  rw [unmap]
  rfl

theorem transport_gradient (e : I ≃ J) (z : CellOf I → K) (u : CellOf I) :
    gradAt (z ∘ (e.prodCongr e).symm) (e.prodCongr e u)=gradAt z u := by
  rw [←grad_formula,←rename_permanent e,pderiv_rename (e.prodCongr e).injective,eval_rename]
  rw [unmap,grad_formula]

theorem transport_rank (e : I ≃ J) (z : CellOf I → K) :
    (hessian (per K J) (z ∘ (e.prodCongr e).symm)).rank=(hessian (per K I) z).rank := by
  let v := e.prodCongr e
  have eq : (hessian (per K J) (z ∘ v.symm)).submatrix v v=hessian (per K I) z := by
    ext u w
    change eval (z ∘ v.symm) (pderiv (v u) (pderiv (v w) (per K J)))=_
    rw [←rename_permanent e,pderiv_rename v.injective,pderiv_rename v.injective,eval_rename]
    rw [unmap]
    rfl
  exact (Matrix.rank_submatrix _ v v).symm.trans (congrArg Matrix.rank eq)

theorem transport_cofactor_rank (e : I ≃ J) (z : CellOf I → K) :
    (cofactor (z ∘ (e.prodCongr e).symm)).rank=(cofactor z).rank := by
  have eq : (cofactor (z ∘ (e.prodCongr e).symm)).submatrix e e=cofactor z := by
    ext i j
    exact transport_gradient e z (i,j)
  exact (Matrix.rank_submatrix _ e e).symm.trans (congrArg Matrix.rank eq)

#print axioms transport_rank
end PermanentBorder
