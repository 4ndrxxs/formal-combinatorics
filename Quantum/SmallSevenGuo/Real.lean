/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Basic

/-!
# Real coordinate constructions

Real vectors with nonzero separating minors determine distinct complex projective rays.
-/

@[expose] public section
set_option maxHeartbeats 0

noncomputable section

namespace QLS7.QuantumLatinSquare

open scoped BigOperators

theorem exists_of_real_coordinates {n r : ℕ} (v : Fin r → Fin n → ℝ)
    (hv : ∀ a, ∃ k, v a k ≠ 0)
    (label : Fin n → Fin n → Fin r)
    (hrow : ∀ i j k, j ≠ k → ∑ l, v (label i j) l * v (label i k) l = 0)
    (hcol : ∀ j i k, i ≠ k → ∑ l, v (label i j) l * v (label k j) l = 0)
    (hdistinct : ∀ a b, a ≠ b → ∃ i j, v a i * v b j ≠ v a j * v b i)
    (hcover : ∀ a, ∃ i j, label i j = a) :
    ∃ q : QuantumLatinSquare n, q.cardinality = r := by
  let w (a : Fin r) : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 fun k => (v a k : ℂ)
  have hw a : w a ≠ 0 := by
    obtain ⟨k, hk⟩ := hv a
    intro h
    have h' : (v a k : ℂ) = 0 := congrArg (fun x : EuclideanSpace ℂ (Fin n) => x k) h
    exact hk (by exact_mod_cast h')
  have hinner a b : inner ℂ (w a) (w b) = ((∑ k, v a k * v b k : ℝ) : ℂ) := by
    simp [w, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  apply exists_of_vectors w hw label
  · intro i j k h
    rw [hinner, hrow i j k h, Complex.ofReal_zero]
  · intro j i k h
    rw [hinner, hcol j i k h, Complex.ofReal_zero]
  · intro a b hab
    by_contra h
    obtain ⟨i, j, hij⟩ := hdistinct a b h
    obtain ⟨z, hz⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).1 hab
    have hi : z * (v b i : ℂ) = (v a i : ℂ) :=
      congrArg (fun x : EuclideanSpace ℂ (Fin n) => x i) hz
    have hj : z * (v b j : ℂ) = (v a j : ℂ) :=
      congrArg (fun x : EuclideanSpace ℂ (Fin n) => x j) hz
    have heq : (v a i : ℂ) * (v b j : ℂ) = (v a j : ℂ) * (v b i : ℂ) := by
      rw [← hi, ← hj]
      ring
    exact hij (by exact_mod_cast heq)
  · exact hcover

end QLS7.QuantumLatinSquare
