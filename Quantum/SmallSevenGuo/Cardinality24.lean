/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.IntegerSoundness

/-!
# An integer certificate of cardinality 24
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality24

def rays : List (List Int) :=
  [[1, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0],
   [1, 1, 0, 0, 0, 0, 0],
   [1, 0, -1, 0, 0, 0, 0],
   [1, 0, 1, 0, 0, 0, 0],
   [1, 0, 0, -1, 0, 0, 0],
   [1, 0, 0, 1, 0, 0, 0],
   [0, 1, -1, 0, 0, 0, 0],
   [0, 1, 1, 0, 0, 0, 0],
   [0, 1, 0, -1, 0, 0, 0],
   [0, 1, 0, 1, 0, 0, 0],
   [0, 0, 1, -1, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 0],
   [1, -1, -1, -1, 0, 0, 0],
   [1, -1, 1, 1, 0, 0, 0],
   [1, 1, -1, 1, 0, 0, 0],
   [1, 1, 1, -1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 1, 0, -1],
   [0, 0, 0, 0, 1, 0, 1]]

def grid : List (List Nat) :=
  [[0, 1, 2, 3, 19, 20, 21],
   [2, 0, 20, 19, 21, 11, 12],
   [20, 21, 7, 10, 16, 17, 19],
   [22, 13, 23, 20, 4, 15, 16],
   [23, 20, 8, 9, 15, 22, 18],
   [3, 19, 1, 21, 20, 6, 5],
   [1, 14, 22, 0, 13, 23, 20]]

def data : IntegerData where
  order := 7
  cardinality := 24
  rays := rays
  grid := grid


theorem rays_shape : rays.length = 24 ∧ ∀ a : Fin 24,
    (rays[a.val]?.getD []).length = 7 := by decide +kernel

theorem grid_shape : grid.length = 7 ∧ ∀ i : Fin 7,
    (grid[i.val]?.getD []).length = 7 := by decide +kernel

theorem labels_in_range : ∀ i j : Fin 7, data.label i.val j.val < 24 := by decide +kernel

theorem all_rays_nonzero : ∀ a : Fin 24, data.dot a.val a.val > 0 := by decide +kernel

theorem row_orthogonality : ∀ i j k : Fin 7, j ≠ k →
    data.dot (data.label i.val j.val) (data.label i.val k.val) = 0 := by decide +kernel

theorem column_orthogonality : ∀ j i k : Fin 7, i ≠ k →
    data.dot (data.label i.val j.val) (data.label k.val j.val) = 0 := by decide +kernel

theorem distinct_projective_rays : ∀ a b : Fin 24, a ≠ b →
    ∃ i j : Fin 7, data.coord a.val i.val * data.coord b.val j.val ≠
      data.coord a.val j.val * data.coord b.val i.val := by decide +kernel

theorem every_ray_appears : ∀ a : Fin 24, ∃ i j : Fin 7,
    data.label i.val j.val = a.val := by decide +kernel


theorem exists_quantumLatinSquare : ∃ q : QuantumLatinSquare 7, q.cardinality = 24 :=
  data.exists_quantumLatinSquare labels_in_range all_rays_nonzero
    row_orthogonality column_orthogonality distinct_projective_rays every_ray_appears

end QLS7.Cardinality24
