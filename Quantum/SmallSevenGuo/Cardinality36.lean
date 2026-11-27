/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.IntegerSoundness

/-!
# An integer certificate of cardinality 36
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality36

def rays : List (List Int) :=
  [[0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 1, -2, -2],
   [0, 0, 0, 0, 1, -1, 0],
   [0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 1, 1, 4],
   [0, 0, 0, 0, 2, -1, 2],
   [0, 0, 0, 0, 2, 2, -1],
   [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0],
   [0, 1, -3, 1, 0, 0, 0],
   [0, 1, -2, 1, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0],
   [0, 1, 2, 3, 0, 0, 0],
   [0, 2, 3, 7, 0, 0, 0],
   [0, 4, 1, -2, 0, 0, 0],
   [0, 24, 5, -9, 0, 0, 0],
   [1, -3, -1, 0, 0, 0, 0],
   [1, -2, 0, -4, 0, 0, 0],
   [1, 0, -3, 2, 0, 0, 0],
   [1, 0, -1, -2, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0],
   [1, 0, 1, 3, 0, 0, 0],
   [1, 2, 1, 0, 0, 0, 0],
   [2, -1, 0, 1, 0, 0, 0],
   [2, 0, 7, -3, 0, 0, 0],
   [2, 1, -4, 0, 0, 0, 0],
   [2, 3, 0, -1, 0, 0, 0],
   [3, -7, 0, 2, 0, 0, 0],
   [3, -2, 1, 0, 0, 0, 0],
   [3, 1, 0, -1, 0, 0, 0],
   [4, 0, 2, 1, 0, 0, 0],
   [5, 9, 0, 24, 0, 0, 0],
   [7, 3, -2, 0, 0, 0, 0],
   [9, -5, 24, 0, 0, 0, 0],
   [24, 0, -9, -5, 0, 0, 0]]

def grid : List (List Nat) :=
  [[4, 1, 0, 13, 19, 27, 29],
   [1, 0, 4, 15, 31, 18, 26],
   [0, 4, 1, 11, 20, 24, 23],
   [14, 10, 16, 21, 3, 5, 7],
   [25, 22, 35, 2, 12, 7, 6],
   [28, 30, 32, 6, 7, 9, 2],
   [33, 17, 34, 7, 5, 3, 8]]

def data : IntegerData where
  order := 7
  cardinality := 36
  rays := rays
  grid := grid


theorem rays_shape : rays.length = 36 ∧ ∀ a : Fin 36,
    (rays[a.val]?.getD []).length = 7 := by decide +kernel

theorem grid_shape : grid.length = 7 ∧ ∀ i : Fin 7,
    (grid[i.val]?.getD []).length = 7 := by decide +kernel

theorem labels_in_range : ∀ i j : Fin 7, data.label i.val j.val < 36 := by decide +kernel

theorem all_rays_nonzero : ∀ a : Fin 36, data.dot a.val a.val > 0 := by decide +kernel

theorem row_orthogonality : ∀ i j k : Fin 7, j ≠ k →
    data.dot (data.label i.val j.val) (data.label i.val k.val) = 0 := by decide +kernel

theorem column_orthogonality : ∀ j i k : Fin 7, i ≠ k →
    data.dot (data.label i.val j.val) (data.label k.val j.val) = 0 := by decide +kernel

theorem distinct_projective_rays : ∀ a b : Fin 36, a ≠ b →
    ∃ i j : Fin 7, data.coord a.val i.val * data.coord b.val j.val ≠
      data.coord a.val j.val * data.coord b.val i.val := by decide +kernel

theorem every_ray_appears : ∀ a : Fin 36, ∃ i j : Fin 7,
    data.label i.val j.val = a.val := by decide +kernel


theorem exists_quantumLatinSquare : ∃ q : QuantumLatinSquare 7, q.cardinality = 36 :=
  data.exists_quantumLatinSquare labels_in_range all_rays_nonzero
    row_orthogonality column_orthogonality distinct_projective_rays every_ray_appears

end QLS7.Cardinality36
