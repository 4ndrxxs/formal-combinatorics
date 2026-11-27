import PermanentFullLine
import Mathlib.Basic.Complex.Basic

/-! Every normalized size-twenty-one representation over the complex numbers
admits arbitrary values on one row or column inside the common zero space of
its two endpoint maps. The two endpoint equations are displayed entrywise. -/

open Matrix PermanentFive QuinticPencil

theorem complex_twenty_one_endpoint_projection
    (b c : Fin 20 → Cell → ℂ) (D : Fin 20 → Fin 20 → Cell → ℂ)
    (identity : per ℂ Idx = regularDet b c D) :
    (∃ r : Fin 5, ∀ y : Fin 5 → ℂ, ∃ x : Fin 5 × Fin 5 → ℂ,
      (∀ a, (∑ j, b a j*x j) = 0) ∧ (∀ a, (∑ j, c a j*x j) = 0) ∧ ∀ j, x (r,j) = y j) ∨
    (∃ k : Fin 5, ∀ y : Fin 5 → ℂ, ∃ x : Fin 5 × Fin 5 → ℂ,
      (∀ a, (∑ j, b a j*x j) = 0) ∧ (∀ a, (∑ j, c a j*x j) = 0) ∧ ∀ j, x (j,k) = y j) := by
  obtain ⟨axis,i,full⟩ := normalized_surjective_line b c D identity (by decide)
  cases axis with
  | false =>
    left
    refine ⟨i,fun y ↦ ?_⟩
    obtain ⟨x,hx,values⟩ := full y
    obtain ⟨a,d⟩ := (endpoint_zero_iff b c x).mp hx
    exact ⟨x,a,d,values⟩
  | true =>
    right
    refine ⟨i,fun y ↦ ?_⟩
    obtain ⟨x,hx,values⟩ := full y
    obtain ⟨a,d⟩ := (endpoint_zero_iff b c x).mp hx
    exact ⟨x,a,d,values⟩

#print axioms complex_twenty_one_endpoint_projection
