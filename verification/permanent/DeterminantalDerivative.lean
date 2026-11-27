import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! The derivative of a polynomial determinant as a sum of determinants
with a single differentiated column. -/

noncomputable section
namespace DeterminantalRegularity
open MvPolynomial Matrix Finset
variable {σ n K : Type*} [CommRing K] [DecidableEq n]

private lemma derivative_product (a : σ) (f : n → MvPolynomial σ K) (s : Finset n) :
    pderiv a (∏ k ∈ s, f k) =
      ∑ j ∈ s, ∏ k ∈ s, if k = j then pderiv a (f k) else f k := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi,pderiv_mul,ih,ite_true]
    rw [Finset.mul_sum]
    congr 1
    · congr 1
      apply Finset.prod_congr rfl
      intro k hk
      have ne : k ≠ i := fun h ↦ hi (h ▸ hk)
      simp [ne]
    · apply Finset.sum_congr rfl
      intro j hj
      have ne : i ≠ j := fun h ↦ hi (h ▸ hj)
      simp [ne]

private lemma derivative_sign (a : σ) (u : ℤˣ) (f : MvPolynomial σ K) :
    pderiv a (u • f) = u • pderiv a f := by
  rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp

/-- The formula uses symbolic partial derivatives and holds over any
commutative coefficient ring. -/
theorem derivative_determinant [Fintype n] (a : σ) (A : Matrix n n (MvPolynomial σ K)) :
    pderiv a A.det = ∑ j, (A.updateCol j (fun i ↦ pderiv a (A i j))).det := by
  rw [Matrix.det_apply,map_sum]
  simp_rw [derivative_sign,derivative_product,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  by_cases h : k = j <;> simp [h]

#print axioms derivative_determinant
end DeterminantalRegularity
