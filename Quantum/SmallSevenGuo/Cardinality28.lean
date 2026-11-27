/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.IntegerSoundness

/-!
# An integer certificate of cardinality 28
-/

@[expose] public section
set_option maxHeartbeats 0

set_option maxRecDepth 1000000

namespace QLS7.Cardinality28

def rays : List (List Int) :=
  [[1, -33, 3, 4, 5, 6, 7],
   [1, -8, 9, -19, 15, 18, 13],
   [1, -6, -9, -12, -13, -25, 13],
   [1, 2, 3, 4, -9, 6, 7],
   [1, 2, 3, 4, 5, 6, -3],
   [1, 30, 3, -4, 3, 13, -11],
   [2, -11, 8, 22, 10, 16, -14],
   [2, 4, 6, -27, 10, 12, 14],
   [3, 6, -61, 12, 15, 18, 21],
   [3, 6, 9, 12, 15, -17, 21],
   [3, 6, 65, 4, -15, -10, 17],
   [3, 8, -9, 19, -13, 10, 21],
   [5, 18, -1, 20, 53, -30, 21],
   [7, -14, 7, -32, 27, 42, 33],
   [9, 10, 1, -48, 17, 30, 35],
   [9, 18, -15, -48, -25, -30, 21],
   [11, 62, -5, -12, -15, -10, -21],
   [11, 62, 9, -4, 15, 18, -17],
   [15, -2, -59, 4, 33, -6, -7],
   [16, -11, -6, -6, -18, 16, -14],
   [16, 4, -8, 15, -18, 12, 14],
   [23, -14, 7, -32, -35, 14, -41],
   [23, 14, 21, 28, -27, 14, 45],
   [29, -9, 11, -4, 3, -6, -11],
   [29, -2, -59, 4, 5, 22, 7],
   [29, -2, 11, 4, 5, -13, 7],
   [57, 2, 3, 4, 33, -22, -7],
   [69, -2, -3, -4, -5, -6, -7]]

def grid : List (List Nat) :=
  [[27, 10, 5, 12, 6, 13, 11],
   [10, 0, 26, 2, 21, 20, 14],
   [5, 26, 8, 22, 1, 15, 19],
   [12, 2, 22, 7, 24, 23, 16],
   [6, 21, 1, 24, 3, 17, 25],
   [13, 20, 15, 23, 17, 9, 18],
   [11, 14, 19, 16, 25, 18, 4]]

def data : IntegerData where
  order := 7
  cardinality := 28
  rays := rays
  grid := grid


theorem rays_shape : rays.length = 28 ∧ ∀ a : Fin 28,
    (rays[a.val]?.getD []).length = 7 := by decide +kernel

theorem grid_shape : grid.length = 7 ∧ ∀ i : Fin 7,
    (grid[i.val]?.getD []).length = 7 := by decide +kernel

theorem labels_in_range : ∀ i j : Fin 7, data.label i.val j.val < 28 := by decide +kernel

theorem all_rays_nonzero : ∀ a : Fin 28, data.dot a.val a.val > 0 := by decide +kernel

theorem row_orthogonality : ∀ i j k : Fin 7, j ≠ k →
    data.dot (data.label i.val j.val) (data.label i.val k.val) = 0 := by decide +kernel

theorem column_orthogonality : ∀ j i k : Fin 7, i ≠ k →
    data.dot (data.label i.val j.val) (data.label k.val j.val) = 0 := by decide +kernel

theorem distinct_projective_rays : ∀ a b : Fin 28, a ≠ b →
    ∃ i j : Fin 7, data.coord a.val i.val * data.coord b.val j.val ≠
      data.coord a.val j.val * data.coord b.val i.val := by decide +kernel

theorem every_ray_appears : ∀ a : Fin 28, ∃ i j : Fin 7,
    data.label i.val j.val = a.val := by decide +kernel


theorem exists_quantumLatinSquare : ∃ q : QuantumLatinSquare 7, q.cardinality = 28 :=
  data.exists_quantumLatinSquare labels_in_range all_rays_nonzero
    row_orthogonality column_orthogonality distinct_projective_rays every_ray_appears

end QLS7.Cardinality28
