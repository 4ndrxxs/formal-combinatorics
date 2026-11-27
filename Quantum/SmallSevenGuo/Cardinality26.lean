/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.IntegerSoundness

/-!
# An integer certificate of cardinality 26
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality26

def rays : List (List Int) :=
  [[0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 1, 0, -1],
   [0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 1, 0, 1],
   [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 1, -1, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0],
   [0, 3, 0, -4, 0, 0, 0],
   [0, 3, 4, 0, 0, 0, 0],
   [0, 4, -3, 0, 0, 0, 0],
   [0, 4, 0, 3, 0, 0, 0],
   [1, -1, 0, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 0],
   [3, -3, -4, 4, 0, 0, 0],
   [3, 0, -4, 0, 0, 0, 0],
   [3, 0, 0, 4, 0, 0, 0],
   [3, 3, -4, -4, 0, 0, 0],
   [3, 3, 4, 4, 0, 0, 0],
   [4, -4, 3, -3, 0, 0, 0],
   [4, 0, 0, -3, 0, 0, 0],
   [4, 0, 3, 0, 0, 0, 0],
   [4, 4, -3, -3, 0, 0, 0],
   [4, 4, 3, 3, 0, 0, 0]]

def grid : List (List Nat) :=
  [[15, 9, 7, 5, 3, 1, 0],
   [7, 15, 1, 3, 0, 13, 10],
   [1, 0, 22, 12, 20, 16, 3],
   [2, 6, 4, 1, 14, 19, 25],
   [4, 1, 18, 11, 24, 2, 21],
   [5, 3, 9, 0, 1, 23, 17],
   [9, 8, 2, 15, 6, 4, 1]]

def data : IntegerData where
  order := 7
  cardinality := 26
  rays := rays
  grid := grid


theorem rays_shape : rays.length = 26 ∧ ∀ a : Fin 26,
    (rays[a.val]?.getD []).length = 7 := by decide +kernel

theorem grid_shape : grid.length = 7 ∧ ∀ i : Fin 7,
    (grid[i.val]?.getD []).length = 7 := by decide +kernel

theorem labels_in_range : ∀ i j : Fin 7, data.label i.val j.val < 26 := by decide +kernel

theorem all_rays_nonzero : ∀ a : Fin 26, data.dot a.val a.val > 0 := by decide +kernel

theorem row_orthogonality : ∀ i j k : Fin 7, j ≠ k →
    data.dot (data.label i.val j.val) (data.label i.val k.val) = 0 := by decide +kernel

theorem column_orthogonality : ∀ j i k : Fin 7, i ≠ k →
    data.dot (data.label i.val j.val) (data.label k.val j.val) = 0 := by decide +kernel

theorem distinct_projective_rays : ∀ a b : Fin 26, a ≠ b →
    ∃ i j : Fin 7, data.coord a.val i.val * data.coord b.val j.val ≠
      data.coord a.val j.val * data.coord b.val i.val := by decide +kernel

theorem every_ray_appears : ∀ a : Fin 26, ∃ i j : Fin 7,
    data.label i.val j.val = a.val := by decide +kernel


theorem exists_quantumLatinSquare : ∃ q : QuantumLatinSquare 7, q.cardinality = 26 :=
  data.exists_quantumLatinSquare labels_in_range all_rays_nonzero
    row_orthogonality column_orthogonality distinct_projective_rays every_ray_appears

end QLS7.Cardinality26
