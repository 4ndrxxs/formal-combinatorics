/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Quantum Latin squares

A quantum Latin square of order `n` is an `n × n` array in `ℂⁿ` with orthonormal rows
and columns. Its cardinality counts distinct complex projective rays.
-/

@[expose] public section
set_option maxHeartbeats 0

noncomputable section

namespace QLS7

/-- An array of vectors in `ℂⁿ` with orthonormal rows and columns. -/
structure QuantumLatinSquare (n : ℕ) where
  entry : Fin n → Fin n → EuclideanSpace ℂ (Fin n)
  row_orthonormal : ∀ i, Orthonormal ℂ (entry i)
  column_orthonormal : ∀ j, Orthonormal ℂ (fun i => entry i j)

namespace QuantumLatinSquare

variable {n r : ℕ}

theorem entry_ne_zero (q : QuantumLatinSquare n) (i j : Fin n) : q.entry i j ≠ 0 := by
  intro h
  have := (q.row_orthonormal i).norm_eq_one j
  simp [h] at this

/-- The projective ray of an entry. -/
def ray (q : QuantumLatinSquare n) (p : Fin n × Fin n) :
    Projectivization ℂ (EuclideanSpace ℂ (Fin n)) :=
  Projectivization.mk ℂ (q.entry p.1 p.2) (q.entry_ne_zero p.1 p.2)

/-- The number of distinct complex projective rays among the entries. -/
def cardinality (q : QuantumLatinSquare n) : ℕ := by
  classical
  exact (Finset.univ.image q.ray).card

theorem ray_normalize (v : EuclideanSpace ℂ (Fin n)) (hv : v ≠ 0) :
    Projectivization.mk ℂ (NormedSpace.normalize v)
      (by simpa using hv) = Projectivization.mk ℂ v hv := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  exact ⟨(‖v‖⁻¹ : ℝ), (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm⟩

/-- Normalize a finite family of nonzero vectors arranged in orthogonal rows and columns. -/
theorem exists_of_vectors
    (v : Fin r → EuclideanSpace ℂ (Fin n)) (hv : ∀ a, v a ≠ 0)
    (label : Fin n → Fin n → Fin r)
    (hrow : ∀ i j k, j ≠ k → inner ℂ (v (label i j)) (v (label i k)) = 0)
    (hcol : ∀ j i k, i ≠ k → inner ℂ (v (label i j)) (v (label k j)) = 0)
    (hdistinct : Function.Injective (fun a => Projectivization.mk ℂ (v a) (hv a)))
    (hcover : ∀ a, ∃ i j, label i j = a) :
    ∃ q : QuantumLatinSquare n, q.cardinality = r := by
  classical
  let entry := fun i j => NormedSpace.normalize (v (label i j))
  have hnorm i j : ‖entry i j‖ = 1 := NormedSpace.norm_normalize (hv _)
  have hinner a b (h : inner ℂ (v a) (v b) = 0) :
      inner ℂ (NormedSpace.normalize (v a)) (NormedSpace.normalize (v b)) = 0 := by
    simp [NormedSpace.normalize, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_left, inner_smul_right, h]
  let q : QuantumLatinSquare n := {
    entry := entry
    row_orthonormal := fun i => ⟨hnorm i, fun j k h => hinner _ _ (hrow i j k h)⟩
    column_orthonormal := fun j => ⟨fun i => hnorm i j, fun i k h => hinner _ _ (hcol j i k h)⟩ }
  refine ⟨q, ?_⟩
  let f := fun a => Projectivization.mk ℂ (v a) (hv a)
  have hray (i j) : q.ray (i, j) = f (label i j) := ray_normalize _ (hv _)
  have himage : Finset.univ.image q.ray = Finset.univ.image f := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨label i j, (hray i j).symm⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨i, j, h⟩ := hcover a
      exact ⟨(i, j), by rw [hray, h]⟩
  change (Finset.univ.image q.ray).card = r
  rw [himage, Finset.card_image_of_injective _ hdistinct]
  simp

end QuantumLatinSquare

end QLS7
