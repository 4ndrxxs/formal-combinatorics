import PermanentShapeClassification
import Mathlib.Basic.Complex.Basic

/-! Conditional dimension and support constraints on a size-twenty-one pencil
over the complex numbers. The nonzero linear relation on each cross is
given by its coefficients in the twenty-five input coordinates. -/

open Matrix Module PermanentFive QuinticPencil

theorem complex_twenty_one_endpoint_constraints
    (b c : Fin 20 → Cell → ℂ) (D : Fin 20 → Fin 20 → Cell → ℂ)
    (identity : per ℂ Idx = regularDet b c D) :
    (finrank ℂ (endpoints b c).ker ∈ ({5,6,7,8,9,10,11,15} : Finset ℕ)) ∧
    (∀ r k : Fin 5, ∃ x : Fin 5 × Fin 5 → ℂ, x ≠ 0 ∧
      (∀ a, (∑ j, b a j*x j) = 0) ∧ (∀ a, (∑ j, c a j*x j) = 0) ∧
      ∀ i j, i ≠ r → j ≠ k → x (i,j) = 0) ∧
    (∀ x : Cell → ℂ, (∀ a, (∑ j, b a j*x j) = 0) → (∀ a, (∑ j, c a j*x j) = 0) →
      IsNilpotent (Matrix.of (fun a d ↦ ∑ j, D a d j*x j))) := by
  refine ⟨kernel_dimension_cases b c D identity (by decide),?_,?_⟩
  · intro r k
    obtain ⟨x,hx,nonzero,support⟩ := kernel_on_every_cross b c D identity (by decide) r k
    obtain ⟨first,second⟩ := (endpoint_zero_iff b c x).mp hx
    exact ⟨x,nonzero,first,second,fun i j ↦ support (i,j)⟩
  · intro x first second
    exact endpoint_transfer_nilpotent b c D identity x ((endpoint_zero_iff b c x).mpr ⟨first,second⟩)

#print axioms complex_twenty_one_endpoint_constraints
