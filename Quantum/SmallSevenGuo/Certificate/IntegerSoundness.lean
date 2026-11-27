/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Basic
public import Quantum.SmallSevenGuo.Certificate.Integer

/-!
# Soundness of integer certificates

Integer dot products give Hermitian inner products after scalar extension to `ℂ`.
Nonzero integer minors distinguish complex projective rays.
-/

@[expose] public section
set_option maxHeartbeats 0

noncomputable section

namespace QLS7.IntegerData

open scoped BigOperators

/-- Interpret an integer coordinate vector in complex Euclidean space. -/
def vector (c : IntegerData) (a : ℕ) : EuclideanSpace ℂ (Fin c.order) :=
  WithLp.toLp 2 fun k => (c.coord a k : ℂ)

theorem dot_eq_sum (c : IntegerData) (a b : ℕ) :
    c.dot a b = ∑ k : Fin c.order, c.coord a k * c.coord b k := by
  rw [Fin.sum_univ_def]
  unfold dot
  change ((List.range c.order).map (fun k => c.coord a k * c.coord b k)).sum =
    ((List.finRange c.order).map ((fun k => c.coord a k * c.coord b k) ∘ Fin.val)).sum
  rw [← List.map_map]
  simp

theorem inner_vector (c : IntegerData) (a b : ℕ) :
    inner ℂ (c.vector a) (c.vector b) = (c.dot a b : ℂ) := by
  rw [dot_eq_sum, Int.cast_sum, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [vector, RCLike.inner_apply, mul_comm]

/-- A valid integer certificate yields a quantum Latin square with the prescribed cardinality. -/
theorem exists_quantumLatinSquare (c : IntegerData)
    (hlabel : ∀ i j : Fin c.order, c.label i j < c.cardinality)
    (hnonzero : ∀ a : Fin c.cardinality, 0 < c.dot a a)
    (hrow : ∀ i j k : Fin c.order, j ≠ k →
      c.dot (c.label i j) (c.label i k) = 0)
    (hcol : ∀ j i k : Fin c.order, i ≠ k →
      c.dot (c.label i j) (c.label k j) = 0)
    (hdistinct : ∀ a b : Fin c.cardinality, a ≠ b → ∃ i j : Fin c.order,
      c.coord a i * c.coord b j ≠ c.coord a j * c.coord b i)
    (hcover : ∀ a : Fin c.cardinality, ∃ i j : Fin c.order, c.label i j = a) :
    ∃ q : QuantumLatinSquare c.order, q.cardinality = c.cardinality := by
  have hv (a : Fin c.cardinality) : c.vector a ≠ 0 := by
    intro h
    have hd := c.inner_vector a a
    rw [h, inner_zero_left] at hd
    have hz : c.dot a a = 0 := by exact_mod_cast hd.symm
    exact (ne_of_gt (hnonzero a)) hz
  let label (i j : Fin c.order) : Fin c.cardinality := ⟨c.label i j, hlabel i j⟩
  apply QuantumLatinSquare.exists_of_vectors (fun a => c.vector a) hv label
  · intro i j k h
    rw [inner_vector, hrow i j k h, Int.cast_zero]
  · intro j i k h
    rw [inner_vector, hcol j i k h, Int.cast_zero]
  · intro a b hab
    by_contra h
    obtain ⟨i, j, hij⟩ := hdistinct a b h
    obtain ⟨z, hz⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).1 hab
    have hi : z * (c.coord b i : ℂ) = (c.coord a i : ℂ) :=
      congrArg (fun v : EuclideanSpace ℂ (Fin c.order) => v i) hz
    have hj : z * (c.coord b j : ℂ) = (c.coord a j : ℂ) :=
      congrArg (fun v : EuclideanSpace ℂ (Fin c.order) => v j) hz
    have heq : (c.coord a i : ℂ) * (c.coord b j : ℂ) =
        (c.coord a j : ℂ) * (c.coord b i : ℂ) := by
      rw [← hi, ← hj]
      ring
    exact hij (by exact_mod_cast heq)
  · intro a
    obtain ⟨i, j, h⟩ := hcover a
    exact ⟨i, j, Fin.ext h⟩

end QLS7.IntegerData
