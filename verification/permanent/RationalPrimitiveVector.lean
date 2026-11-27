import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Specialization of linear spaces at the origin of a rational-function parameter. -/

noncomputable section
open Polynomial Module
namespace RationalSpecialization
variable {K I : Type*} [Field K] [Fintype I]

/-- Clear all denominators and remove the largest common power of the parameter. -/
theorem primitive_vector (v : I → RatFunc K) (nv : v ≠ 0) :
    ∃ (c : RatFunc K) (p : I → K[X]), c ≠ 0 ∧
      (∀ i, algebraMap K[X] (RatFunc K) (p i) = c * v i) ∧
      ∃ j, (p j).eval 0 ≠ 0 := by
  classical
  let φ := algebraMap K[X] (RatFunc K)
  obtain ⟨b,hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors K[X]) v
  have clear (i : I) : ∃ a : K[X], φ a = φ b * v i := by
    obtain ⟨a,ha⟩ := hb i
    exact ⟨a,ha.trans (Algebra.smul_def _ _)⟩
  choose f hf using clear
  have nb : φ b ≠ 0 := fun h ↦ nonZeroDivisors.coe_ne_zero b
    (RatFunc.algebraMap_injective K (h.trans φ.map_zero.symm))
  have nz : ∃ n : ℕ, ∃ i, (f i).coeff n ≠ 0 := by
    by_contra! h
    apply nv
    funext i
    have z : f i = 0 := by ext n; simp [h n i]
    have hmul := hf i
    rw [z,map_zero] at hmul
    exact (mul_eq_zero.mp hmul.symm).resolve_left nb
  let d := Nat.find nz
  obtain ⟨j,hj⟩ := Nat.find_spec nz
  have divides (i : I) : X^d ∣ f i := by
    apply X_pow_dvd_iff.mpr
    intro e he
    by_contra hn
    exact Nat.find_min nz he ⟨i,hn⟩
  choose p hp using divides
  have nx : φ (X^d) ≠ 0 := fun h ↦ pow_ne_zero d (X_ne_zero (R := K))
    (RatFunc.algebraMap_injective K (h.trans φ.map_zero.symm))
  refine ⟨φ b / φ (X^d),p,div_ne_zero nb nx,?_,j,?_⟩
  · intro i
    have eq := hf i
    rw [hp i,map_mul] at eq
    field_simp [nx]
    linear_combination eq
  · intro h
    apply hj
    change (f j).coeff d = 0
    rw [hp j,coeff_X_pow_mul']
    simpa [coeff_zero_eq_eval_zero] using h

#print axioms primitive_vector
end RationalSpecialization
