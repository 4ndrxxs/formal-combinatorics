/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.IntegerSoundness

/-!
# An integer certificate of cardinality 27
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality27

def rays : List (List Int) :=
  [[1, 0, 0, 0, 0, 0, 0],
   [0, 1, 0, 0, 0, 0, 0],
   [0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0],
   [1, -1, 0, 0, 0, 0, 0],
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
   [1, -1, -1, 1, 0, 0, 0],
   [1, -1, 1, -1, 0, 0, 0],
   [1, 1, -1, -1, 0, 0, 0],
   [1, 1, 1, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 1, -1, 0],
   [0, 0, 0, 0, 1, 1, 0],
   [0, 0, 0, 0, 1, 0, -1],
   [0, 0, 0, 0, 1, 0, 1]]

def grid : List (List Nat) :=
  [[0, 1, 2, 3, 20, 21, 22],
   [22, 6, 12, 24, 19, 17, 23],
   [23, 7, 13, 22, 16, 18, 24],
   [1, 25, 26, 2, 21, 9, 8],
   [14, 21, 25, 4, 18, 26, 19],
   [24, 3, 0, 23, 22, 11, 10],
   [15, 26, 21, 5, 17, 25, 16]]

def data : IntegerData where
  order := 7
  cardinality := 27
  rays := rays
  grid := grid


theorem rays_shape : rays.length = 27 ∧ ∀ a : Fin 27,
    (rays[a.val]?.getD []).length = 7 := by decide +kernel

theorem grid_shape : grid.length = 7 ∧ ∀ i : Fin 7,
    (grid[i.val]?.getD []).length = 7 := by decide +kernel

theorem labels_in_range : ∀ i j : Fin 7, data.label i.val j.val < 27 := by decide +kernel

theorem all_rays_nonzero : ∀ a : Fin 27, data.dot a.val a.val > 0 := by decide +kernel

theorem row_orthogonality : ∀ i j k : Fin 7, j ≠ k →
    data.dot (data.label i.val j.val) (data.label i.val k.val) = 0 := by decide +kernel

theorem column_orthogonality : ∀ j i k : Fin 7, i ≠ k →
    data.dot (data.label i.val j.val) (data.label k.val j.val) = 0 := by decide +kernel

theorem distinct_projective_rays : ∀ a b : Fin 27, a ≠ b →
    ∃ i j : Fin 7, data.coord a.val i.val * data.coord b.val j.val ≠
      data.coord a.val j.val * data.coord b.val i.val := by decide +kernel

theorem every_ray_appears : ∀ a : Fin 27, ∃ i j : Fin 7,
    data.label i.val j.val = a.val := by decide +kernel


theorem exists_quantumLatinSquare : ∃ q : QuantumLatinSquare 7, q.cardinality = 27 :=
  data.exists_quantumLatinSquare labels_in_range all_rays_nonzero
    row_orthogonality column_orthogonality distinct_projective_rays every_ray_appears

end QLS7.Cardinality27
