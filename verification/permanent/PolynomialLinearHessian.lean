import PermanentOrderTransport
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! First and second symbolic derivatives under a homogeneous linear
change of coordinates, over an arbitrary field. -/
noncomputable section
open Matrix Finset MvPolynomial QuinticPencil
namespace PolynomialLinearChange
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
def form (a : I → K) : MvPolynomial I K := ∑ j, C (a j)*X j
def subst (M : Matrix I I K) : MvPolynomial I K →+* MvPolynomial I K :=
  eval₂Hom C (fun i ↦ form (M i))

omit [DecidableEq I] in
@[simp] theorem subst_X (M : Matrix I I K) (i : I) : subst M (X i)=form (M i) := by simp [subst]
omit [DecidableEq I] in
@[simp] theorem subst_C (M : Matrix I I K) (a : K) : subst M (C a)=C a := by simp [subst]
theorem pderiv_form (a : I → K) (i : I) : pderiv i (form a)=C (a i) := by
  simp [form,Pi.single_apply,mul_ite]
omit [DecidableEq I] in
theorem eval_form (a z : I → K) : eval z (form a)=a ⬝ᵥ z := by simp [form,dotProduct]

omit [DecidableEq I] in
theorem eval_subst (M : Matrix I I K) (p : MvPolynomial I K) (z : I → K) :
    eval z (subst M p)=eval (M *ᵥ z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p j hp => simp [hp,eval_form,Matrix.mulVec]

theorem pderiv_subst (M : Matrix I I K) (p : MvPolynomial I K) (i : I) :
    pderiv i (subst M p)=∑ j, C (M j i)*subst M (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq,mul_add,Finset.sum_add_distrib]
  | mul_X p t hp =>
    simp only [map_mul,pderiv_mul,hp,subst_X,pderiv_form,map_add,mul_add,Finset.sum_add_distrib]
    rw [Finset.sum_mul]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · simp [pderiv_X,Pi.single_apply,apply_ite,mul_comm]

theorem grad_chain (M : Matrix I I K) (p : MvPolynomial I K) (z : I → K) (i : I) :
    eval z (pderiv i (subst M p))=∑ j, M j i*eval (M *ᵥ z) (pderiv j p) := by
  simp [pderiv_subst,eval_subst]

theorem hess_chain (M : Matrix I I K) (p : MvPolynomial I K) (z : I → K) :
    hessian (subst M p) z=M.transpose*hessian p (M *ᵥ z)*M := by
  ext i j
  change eval z (pderiv i (pderiv j (subst M p)))=_
  rw [pderiv_subst]
  simp only [map_sum,pderiv_C_mul,map_mul,eval_C,grad_chain,Matrix.mul_apply,Matrix.transpose_apply,
    hessian,Matrix.of_apply,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem rank_le_under_symmetry (M : Matrix I I K) (p : MvPolynomial I K) (z : I → K) (a : K)
    (law : subst M p=C a*p) (nz : a≠0) : (hessian p z).rank≤(hessian p (M *ᵥ z)).rank := by
  have chain := hess_chain M p z
  have left : hessian (subst M p) z=a • hessian p z := by
    rw [law]
    ext i j
    simp [hessian,Matrix.smul_apply]
  have le := (Matrix.rank_mul_le_left (M.transpose*hessian p (M *ᵥ z)) M).trans
    (Matrix.rank_mul_le_right _ _)
  rw [←chain,left,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero nz)] at le
  exact le

#print axioms hess_chain
end PolynomialLinearChange
