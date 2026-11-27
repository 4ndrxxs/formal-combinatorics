/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Mathlib.NumberTheory.Real.Irrational

public import Quantum.SmallSevenGuo.Real

public import Quantum.SmallSevenGuo.Certificate.Integer

/-!
# A certificate over ℚ(√3) of cardinality 37
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality37

abbrev Quad := Int × Int

def rays : List (List Quad) :=
  [[(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (1, 0)],
   [(0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (1, 0), (0, 0)],
   [(0, 0), (0, 0), (0, 0), (0, 0), (1, 0), (0, 0), (0, 0)],
   [(0, 0), (0, 0), (0, 0), (1, 0), (0, 0), (0, 0), (0, 0)],
   [(0, 0), (0, 0), (1, -1), (1, 1), (2, 0), (-2, 0), (0, 0)],
   [(0, 0), (0, 0), (1, 0), (0, 0), (0, 0), (0, 0), (0, 0)],
   [(0, 0), (0, 0), (1, 1), (1, -1), (2, 0), (-2, 0), (0, 0)],
   [(0, 0), (1, -1), (-2, 0), (0, 0), (-1, -1), (-2, 0), (0, 0)],
   [(0, 0), (1, -1), (0, 0), (-2, 0), (-1, -1), (-2, 0), (0, 0)],
   [(0, 0), (1, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)],
   [(0, 0), (1, 0), (1, 0), (1, 0), (-1, 0), (0, 0), (-2, 0)],
   [(0, 0), (1, 0), (1, 0), (1, 0), (-1, 0), (0, 0), (2, 0)],
   [(0, 0), (1, 1), (-2, 0), (0, 0), (-1, 1), (-2, 0), (0, 0)],
   [(0, 0), (1, 1), (0, 0), (-2, 0), (-1, 1), (-2, 0), (0, 0)],
   [(0, 0), (2, 0), (-1, -1), (-1, 1), (0, 0), (2, 0), (0, 0)],
   [(0, 0), (2, 0), (-1, 1), (-1, -1), (0, 0), (2, 0), (0, 0)],
   [(1, -1), (0, 0), (0, 0), (2, 0), (-2, 0), (-1, -1), (0, 0)],
   [(1, -1), (0, 0), (2, 0), (0, 0), (-2, 0), (-1, -1), (0, 0)],
   [(1, -1), (2, 0), (0, 0), (2, 0), (0, 0), (-1, -1), (0, 0)],
   [(1, -1), (2, 0), (2, 0), (0, 0), (0, 0), (-1, -1), (0, 0)],
   [(1, 0), (-1, 0), (0, 0), (0, 0), (1, 0), (-1, 0), (-2, 0)],
   [(1, 0), (-1, 0), (0, 0), (0, 0), (1, 0), (-1, 0), (2, 0)],
   [(1, 0), (0, 0), (-1, 0), (-1, 0), (0, 0), (-1, 0), (-2, 0)],
   [(1, 0), (0, 0), (-1, 0), (-1, 0), (0, 0), (-1, 0), (2, 0)],
   [(1, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)],
   [(1, 1), (0, 0), (0, 0), (2, 0), (-2, 0), (-1, 1), (0, 0)],
   [(1, 1), (0, 0), (2, 0), (0, 0), (-2, 0), (-1, 1), (0, 0)],
   [(1, 1), (2, 0), (0, 0), (2, 0), (0, 0), (-1, 1), (0, 0)],
   [(1, 1), (2, 0), (2, 0), (0, 0), (0, 0), (-1, 1), (0, 0)],
   [(2, 0), (-2, 0), (1, -1), (1, 1), (0, 0), (0, 0), (0, 0)],
   [(2, 0), (-2, 0), (1, 1), (1, -1), (0, 0), (0, 0), (0, 0)],
   [(2, 0), (0, 0), (1, -1), (1, 1), (2, 0), (0, 0), (0, 0)],
   [(2, 0), (0, 0), (1, 1), (1, -1), (2, 0), (0, 0), (0, 0)],
   [(2, 0), (1, -1), (-2, 0), (0, 0), (-1, -1), (0, 0), (0, 0)],
   [(2, 0), (1, -1), (0, 0), (-2, 0), (-1, -1), (0, 0), (0, 0)],
   [(2, 0), (1, 1), (-2, 0), (0, 0), (-1, 1), (0, 0), (0, 0)],
   [(2, 0), (1, 1), (0, 0), (-2, 0), (-1, 1), (0, 0), (0, 0)]]

def grid : List (List Nat) :=
  [[11, 6, 8, 12, 15, 10, 24],
   [4, 23, 25, 17, 22, 32, 9],
   [13, 16, 20, 21, 27, 34, 5],
   [7, 26, 21, 20, 19, 35, 3],
   [14, 22, 18, 28, 23, 29, 2],
   [10, 31, 36, 33, 30, 11, 1],
   [24, 9, 5, 3, 2, 1, 0]]

def vec (a k : Nat) : Quad := (rays[a]?.getD [])[k]?.getD (0, 0)
def label (i j : Nat) : Nat := (grid[i]?.getD [])[j]?.getD 37
def mul (x y : Quad) : Quad := (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def sub (x y : Quad) : Quad := (x.1 - y.1, x.2 - y.2)
def dot0 (a b : Nat) : Int :=
  ((List.range 7).map (fun k => (mul (vec a k) (vec b k)).1)).sum
def dot1 (a b : Nat) : Int :=
  ((List.range 7).map (fun k => (mul (vec a k) (vec b k)).2)).sum
def minor (a b i j : Nat) : Quad :=
  sub (mul (vec a i) (vec b j)) (mul (vec a j) (vec b i))

theorem rays_shape : rays.length = 37 ∧ ∀ a : Fin 37,
    (rays[a.val]?.getD []).length = 7 := by decide +kernel
theorem grid_shape : grid.length = 7 ∧ ∀ i : Fin 7,
    (grid[i.val]?.getD []).length = 7 := by decide +kernel
theorem labels_in_range : ∀ i j : Fin 7, label i.val j.val < 37 := by decide +kernel
theorem squared_norms_real_positive : ∀ a : Fin 37,
    dot0 a.val a.val > 0 ∧ dot1 a.val a.val = 0 := by decide +kernel
theorem row_orthogonality : ∀ i j k : Fin 7, j ≠ k →
    dot0 (label i.val j.val) (label i.val k.val) = 0 ∧
    dot1 (label i.val j.val) (label i.val k.val) = 0 := by decide +kernel
theorem column_orthogonality : ∀ j i k : Fin 7, i ≠ k →
    dot0 (label i.val j.val) (label k.val j.val) = 0 ∧
    dot1 (label i.val j.val) (label k.val j.val) = 0 := by decide +kernel
theorem distinct_projective_rays : ∀ a b : Fin 37, a ≠ b →
    ∃ i j : Fin 7, minor a.val b.val i.val j.val ≠ (0, 0) := by decide +kernel
theorem every_ray_appears : ∀ a : Fin 37, ∃ i j : Fin 7,
    label i.val j.val = a.val := by decide +kernel

noncomputable section

open scoped BigOperators

/-- Interpret a pair of integers as an element of `ℚ(√3)` in `ℝ`. -/
def eval (x : Quad) : ℝ := x.1 + x.2 * Real.sqrt 3

theorem eval_mul (x y : Quad) : eval (mul x y) = eval x * eval y := by
  simp only [eval, mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem eval_sub (x y : Quad) : eval (sub x y) = eval x - eval y := by
  simp only [eval, sub, Int.cast_sub]
  ring

theorem eval_eq_zero_iff (x : Quad) : eval x = 0 ↔ x = (0, 0) := by
  rcases x with ⟨a, b⟩
  constructor
  · intro h
    have hb : b = 0 := by
      by_contra hb
      have hirr : Irrational (Real.sqrt (3 : ℝ)) := by
        simpa using (show Nat.Prime 3 by decide).irrational_sqrt
      exact ((hirr.intCast_mul hb).intCast_add a).ne_int 0 (by simpa [eval] using h)
    have ha : a = 0 := by simpa [eval, hb] using h
    exact Prod.ext ha hb
  · intro h
    rw [h]
    simp [eval]

theorem dot_eval (a b : ℕ) :
    ∑ k : Fin 7, eval (vec a k) * eval (vec b k) =
      (dot0 a b : ℝ) + (dot1 a b : ℝ) * Real.sqrt 3 := by
  have sum_eq (f : ℕ → ℤ) :
      (((List.range 7).map f).sum : ℝ) = ∑ k : Fin 7, (f k : ℝ) := by
    rw [← Int.cast_sum]
    congr 1
  simp_rw [← eval_mul]
  simp only [dot0, dot1, sum_eq, eval, Finset.sum_add_distrib, Finset.sum_mul]

theorem exists_quantumLatinSquare : ∃ q : QuantumLatinSquare 7, q.cardinality = 37 := by
  let v (a : Fin 37) (k : Fin 7) := eval (vec a k)
  have hv (a : Fin 37) : ∃ k, v a k ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ∑ k : Fin 7, v a k * v a k = 0 := by simp [h]
    change ∑ k : Fin 7, eval (vec a k) * eval (vec a k) = 0 at hz
    rw [dot_eval, (squared_norms_real_positive a).2, Int.cast_zero, zero_mul, add_zero] at hz
    exact (ne_of_gt (squared_norms_real_positive a).1) (by exact_mod_cast hz)
  let labels (i j : Fin 7) : Fin 37 := ⟨label i j, labels_in_range i j⟩
  apply QuantumLatinSquare.exists_of_real_coordinates v hv labels
  · intro i j k h
    obtain ⟨h0, h1⟩ := row_orthogonality i j k h
    change ∑ l : Fin 7, eval (vec (label i j) l) * eval (vec (label i k) l) = 0
    rw [dot_eval, h0, h1]
    simp
  · intro j i k h
    obtain ⟨h0, h1⟩ := column_orthogonality j i k h
    change ∑ l : Fin 7, eval (vec (label i j) l) * eval (vec (label k j) l) = 0
    rw [dot_eval, h0, h1]
    simp
  · intro a b h
    obtain ⟨i, j, hij⟩ := distinct_projective_rays a b h
    refine ⟨i, j, ?_⟩
    intro heq
    apply hij
    apply (eval_eq_zero_iff _).1
    rw [minor, eval_sub, eval_mul, eval_mul]
    exact sub_eq_zero.mpr heq
  · intro a
    obtain ⟨i, j, h⟩ := every_ray_appears a
    exact ⟨i, j, Fin.ext h⟩

end

end QLS7.Cardinality37
