import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

/-! Adding constants to the linear factors of a product affects only terms
below its top possible total degree. -/
noncomputable section
namespace DegreeDrop
open Finset MvPolynomial
variable {K I J : Type*} [Field K] [DecidableEq J]

omit [DecidableEq J] in
theorem product_degree_le_card (S : Finset J) (a : J → MvPolynomial I K)
    (degree : ∀ j, (a j).totalDegree ≤ 1) : (∏ j ∈ S, a j).totalDegree ≤ S.card := by
  exact (totalDegree_finsetProd S a).trans (by simpa using
    (Finset.sum_le_sum (s:=S) (f:=fun j ↦ (a j).totalDegree) (g:=fun _ ↦ 1) (fun j _ ↦ degree j)))

theorem product_add_constants (S : Finset J) (a : J → MvPolynomial I K) (z : J → K)
    (degree : ∀ j, (a j).totalDegree ≤ 1) :
    ∃ p : MvPolynomial I K, p.totalDegree ≤ S.card-1 ∧
      (∏ j ∈ S, (a j + C (z j))) = (∏ j ∈ S, a j)+p := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,by simp,by simp⟩
  | @insert i S hi ih =>
    by_cases empty : S = ∅
    · subst S
      exact ⟨C (z i),by simp,by simp⟩
    obtain ⟨p,deg,eq⟩ := ih
    let q := a i * p + C (z i) * (∏ j ∈ S, a j) + C (z i) * p
    refine ⟨q,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hi,Nat.add_sub_cancel]
      have pos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
      have left := totalDegree_mul (a i) p
      have middle := totalDegree_mul (C (z i) : MvPolynomial I K) (∏ j ∈ S, a j)
      have right := totalDegree_mul (C (z i) : MvPolynomial I K) p
      simp only [totalDegree_C,zero_add] at middle right
      have d := degree i
      have bound := product_degree_le_card S a degree
      exact (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le (by omega) (by omega))) (by omega))
    · simp only [Finset.prod_insert hi,eq,q]
      ring

#print axioms product_add_constants
end DegreeDrop
