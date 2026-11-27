import QuinticDerivatives
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! The ordinary directional second derivative is the quadratic form of
the matrix of symbolic second partials. -/

noncomputable section
open Polynomial
namespace QuinticPencil
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

private def alongPoly (y z : I → K) : MvPolynomial I K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i ↦ Polynomial.C (y i) + X * Polynomial.C (z i))

private def dir (z : I → K) : Derivation K (MvPolynomial I K) (MvPolynomial I K) :=
  ∑ i : I, (MvPolynomial.C (z i) : MvPolynomial I K) •
    (MvPolynomial.pderiv i : Derivation K (MvPolynomial I K) (MvPolynomial I K))

omit [DecidableEq I] in
private theorem dir_apply (z : I → K) (p : MvPolynomial I K) :
    dir z p = ∑ i, MvPolynomial.C (z i) * MvPolynomial.pderiv i p := by
  simp only [dir,sum_apply,smul_apply,smul_eq_mul]

private theorem dir_X (z : I → K) (j : I) :
    dir z (MvPolynomial.X j) = MvPolynomial.C (z j) := by
  classical
  simp [dir_apply,MvPolynomial.pderiv_X,Pi.single_apply,mul_ite]

omit [DecidableEq I] in
private theorem dir_C (z : I → K) (r : K) : dir z (MvPolynomial.C r) = 0 :=
  (dir z).map_algebraMap r

private theorem chain (y z : I → K) (p : MvPolynomial I K) :
    (alongPoly y z p).derivative = alongPoly y z (dir z p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [dir_C]; simp [alongPoly]
  | add p q hp hq => simp [hp,hq]
  | mul_X p j ih =>
    rw [map_mul,Polynomial.derivative_mul,ih,Derivation.leibniz,dir_X]
    simp only [smul_eq_mul,map_add,map_mul]
    have ex : alongPoly y z (MvPolynomial.X j) = Polynomial.C (y j) + X * Polynomial.C (z j) := by simp [alongPoly]
    have ec : alongPoly y z (MvPolynomial.C (z j)) = Polynomial.C (z j) := by simp [alongPoly]
    rw [ex,ec]
    simp only [Polynomial.derivative_add,Polynomial.derivative_C,Polynomial.derivative_mul,Polynomial.derivative_X,
      zero_add,one_mul,mul_zero,add_zero]
    ring

omit [Fintype I] [DecidableEq I] in
private theorem alongPoly_eval (y z : I → K) (p : MvPolynomial I K) (t : K) :
    (alongPoly y z p).eval t = MvPolynomial.eval (y + t • z) p := by
  change Polynomial.evalRingHom t (MvPolynomial.eval₂Hom _ _ p) = _
  rw [MvPolynomial.map_eval₂Hom]
  have cmp : (Polynomial.evalRingHom t).comp (Polynomial.C : K →+* K[X]) = RingHom.id K := by
    ext a; simp
  simp only [cmp,Polynomial.coe_evalRingHom,map_add,map_mul,Polynomial.eval_C,Polynomial.eval_X]
  rfl

omit [DecidableEq I] in
private theorem dir_twice (z : I → K) (p : MvPolynomial I K) :
    dir z (dir z p) = ∑ i, ∑ j, MvPolynomial.C (z i) *
      (MvPolynomial.C (z j) * MvPolynomial.pderiv j (MvPolynomial.pderiv i p)) := by
  rw [dir_apply z p,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Derivation.leibniz,dir_C,dir_apply]
  simp [smul_eq_mul,Finset.mul_sum]

/-- Evaluate the second derivative of the line restriction at zero. -/
theorem directional_second (p : MvPolynomial I K) (y z : I → K) :
    ((alongPoly y z p).derivative.derivative).eval 0 = (hessian p y).toBilin' z z := by
  rw [chain,chain,alongPoly_eval,zero_smul,add_zero,dir_twice,Matrix.toBilin'_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_C,MvPolynomial.pderiv_comm j i]
  simp only [hessian,Matrix.of_apply]
  ring

/-- An even second difference vanishing along the whole line forces the
Hessian quadratic form to vanish in that direction. -/
theorem hessian_zero_of_even [CharZero K] (p : MvPolynomial I K) (y z : I → K)
    (even : ∀ t : K, MvPolynomial.eval (y+t•z) p + MvPolynomial.eval (y-t•z) p =
      2 * MvPolynomial.eval y p) : (hessian p y).toBilin' z z = 0 := by
  let q := alongPoly y z p
  have eq : q + q.comp (-X) = Polynomial.C (2 * MvPolynomial.eval y p) := by
    apply Polynomial.funext
    intro t
    simpa [q,Polynomial.eval_comp,alongPoly_eval,sub_eq_add_neg] using even t
  have h := congrArg (fun g : K[X] ↦ g.derivative.derivative.eval 0) eq
  simp [Polynomial.derivative_comp,Polynomial.eval_comp] at h
  rw [← directional_second]
  change q.derivative.derivative.eval 0 = 0
  exact h

#print axioms directional_second
#print axioms hessian_zero_of_even
end QuinticPencil
