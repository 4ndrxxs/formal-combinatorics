/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.IntegerSoundness

/-!
# An integer certificate of cardinality 39
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality39

def rays : List (List Int) :=
  [[0, 52, 0, 0, 39, -25, 0],
   [0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 4, 0, 0, -3],
   [0, 4, 0, 0, 3, 13, 0],
   [0, 0, 0, 3, 0, 0, 4],
   [0, 3, 0, 0, -4, 0, 0],
   [1, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0],
   [60, 0, 0, 0, 39, -25, 0],
   [36, 0, 0, 0, -65, -15, 0],
   [0, 0, 12, 0, 0, 0, 5],
   [5, 0, 0, 0, 0, 12, 0],
   [0, 0, 5, 0, 0, 0, -12],
   [0, 1, 0, 0, 0, 0, 0],
   [0, 36, 0, 0, -48, 0, 25],
   [0, 0, 0, 36, 25, 39, 48],
   [0, 0, 0, 108, 75, -325, 144],
   [0, 25, 0, 48, 0, 0, -36],
   [0, 48, 0, -25, 36, 0, 0],
   [0, 0, 20, 0, -25, -39, -48],
   [20, 0, 0, 0, 0, 48, -39],
   [0, 0, 20, 0, 169, -39, -48],
   [48, 0, -39, 0, 0, -20, 0],
   [39, 0, 48, 0, 0, 0, 20],
   [0, 25, 15, 0, 0, 52, -36],
   [45, 0, 0, -325, 0, 108, 156],
   [15, 0, 0, 39, 0, 36, 52],
   [0, 169, -15, 0, 0, -52, 36],
   [36, 0, 52, 0, 0, -15, 0],
   [52, 0, -36, 0, 0, 0, -15],
   [0, 0, 0, 0, 1, 0, 0],
   [0, 15, -169, 0, -20, 0, -60],
   [39, 0, 0, 15, -60, 0, 20],
   [65, 0, 0, -9, 36, 0, -12],
   [0, 3, 5, 0, -4, 0, -12],
   [0, 12, 0, -4, 0, 0, 3],
   [0, 4, 0, 12, 3, 0, 0],
   [0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 1]]

def grid : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6],
   [7, 8, 9, 10, 11, 12, 13],
   [14, 15, 16, 6, 17, 18, 1],
   [19, 20, 13, 21, 22, 23, 7],
   [24, 25, 26, 27, 28, 29, 30],
   [31, 32, 33, 34, 35, 36, 37],
   [6, 13, 1, 7, 30, 37, 38]]

def data : IntegerData where
  order := 7
  cardinality := 39
  rays := rays
  grid := grid


theorem rays_shape : rays.length = 39 ∧ ∀ a : Fin 39,
    (rays[a.val]?.getD []).length = 7 := by decide +kernel

theorem grid_shape : grid.length = 7 ∧ ∀ i : Fin 7,
    (grid[i.val]?.getD []).length = 7 := by decide +kernel

theorem labels_in_range : ∀ i j : Fin 7, data.label i.val j.val < 39 := by decide +kernel

theorem all_rays_nonzero : ∀ a : Fin 39, data.dot a.val a.val > 0 := by decide +kernel

theorem row_orthogonality : ∀ i j k : Fin 7, j ≠ k →
    data.dot (data.label i.val j.val) (data.label i.val k.val) = 0 := by decide +kernel

theorem column_orthogonality : ∀ j i k : Fin 7, i ≠ k →
    data.dot (data.label i.val j.val) (data.label k.val j.val) = 0 := by decide +kernel

theorem distinct_projective_rays : ∀ a b : Fin 39, a ≠ b →
    ∃ i j : Fin 7, data.coord a.val i.val * data.coord b.val j.val ≠
      data.coord a.val j.val * data.coord b.val i.val := by decide +kernel

theorem every_ray_appears : ∀ a : Fin 39, ∃ i j : Fin 7,
    data.label i.val j.val = a.val := by decide +kernel


theorem exists_quantumLatinSquare : ∃ q : QuantumLatinSquare 7, q.cardinality = 39 :=
  data.exists_quantumLatinSquare labels_in_range all_rays_nonzero
    row_orthogonality column_orthogonality distinct_projective_rays every_ray_appears

end QLS7.Cardinality39
