/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Basic

/-!
# Integer certificates

Integer vectors and a square array of labels. Nonzero minors distinguish the associated rays.
-/

@[expose] public section
set_option maxHeartbeats 0

namespace QLS7

/-- Data for a square whose entries are labelled integer vectors. -/
structure IntegerData where
  order : Nat
  cardinality : Nat
  rays : List (List Int)
  grid : List (List Nat)

namespace IntegerData

def coord (c : IntegerData) (a k : Nat) : Int :=
  (c.rays[a]?.getD [])[k]?.getD 0

def label (c : IntegerData) (i j : Nat) : Nat :=
  (c.grid[i]?.getD [])[j]?.getD c.cardinality

def dot (c : IntegerData) (a b : Nat) : Int :=
  ((List.range c.order).map fun k => c.coord a k * c.coord b k).sum

end IntegerData

end QLS7
