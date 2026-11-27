import PermanentWeightedEquiv
import Mathlib.Algebra.Polynomial.Derivative

/-! Constant directional derivatives and affine polynomial substitution. -/
noncomputable section
open Matrix Finset MvPolynomial
namespace PermanentJets
variable {R I J : Type*} [CommRing R] [Fintype I] [Fintype J]

def dir (u : I→R) : Derivation R (MvPolynomial I R) (MvPolynomial I R) :=
  ∑ i : I, (C (u i):MvPolynomial I R) • (pderiv (R:=R) i)

theorem dir_apply (u : I→R) (p : MvPolynomial I R) :
    dir u p=∑ i, C (u i)*pderiv i p := by simp [dir,smul_eq_mul]

@[simp] theorem dir_C (u : I→R) (a : R) : dir u (C a)=0 := by simp
@[simp] theorem dir_X (u : I→R) (i : I) : dir u (X i)=C (u i) := by
  classical
  simp [dir_apply,pderiv_X,Pi.single_apply,mul_ite]
@[simp] theorem dir_const_mul (u : I→R) (a : R) (p : MvPolynomial I R) :
    dir u (C a*p)=C a*dir u p := by
  simp [Derivation.leibniz,smul_eq_mul]

theorem dir_addv (u v : I→R) : dir (u+v)=dir u+dir v := by
  simp [dir,add_smul,Finset.sum_add_distrib]
theorem dir_subv (u v : I→R) : dir (u-v)=dir u-dir v := by
  ext1 p
  simp [dir_apply,sub_mul,Finset.sum_sub_distrib]
theorem dir_smulv (a : R) (u : I→R) : dir (a • u)=(C a:MvPolynomial I R) • dir u := by
  simp [dir,Finset.smul_sum,mul_smul,smul_eq_mul]
theorem dir_single [DecidableEq I] (i : I) : dir (Pi.single i (1:R))=pderiv i := by
  simp [dir,Pi.single_apply,apply_ite C,ite_smul]
theorem dir_comm (u v : I→R) (p : MvPolynomial I R) : dir u (dir v p)=dir v (dir u p) := by
  simp only [dir_apply,map_sum,pderiv_C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pderiv_comm i j]
  ring

theorem affine_chain (x : I→MvPolynomial J R) (w : I→R) (v : J→R)
    (h : ∀ i,dir v (x i)=C (w i)) (p : MvPolynomial I R) :
    dir v (eval₂Hom C x p)=eval₂Hom C x (dir w p) := by
  change dir v (bind₁ x p)=bind₁ x (dir w p)
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [Derivation.leibniz,smul_eq_mul,h,hp]

theorem dir_hessian (p : MvPolynomial I R) (z w : I→R) (e : I) :
    eval z (dir w (pderiv e p))=(QuinticPencil.hessian p z *ᵥ w) e := by
  simp only [dir_apply,map_sum,map_mul,eval_C,Matrix.mulVec,dotProduct,QuinticPencil.hessian,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [pderiv_comm j e,mul_comm]

end PermanentJets
