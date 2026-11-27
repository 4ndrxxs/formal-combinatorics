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
# Polynomial arithmetic for certificates

Coefficient lists are in increasing degree order. This representation permits direct reduction
of the polynomial identities in the certificates.
-/

@[expose] public section
set_option maxHeartbeats 0

namespace QLS7

/-- An integer polynomial represented by its coefficients in increasing degree order. -/
abbrev IntPolynomial := List Int

namespace IntPolynomial

def trim (p : IntPolynomial) : IntPolynomial :=
  (p.reverse.dropWhile (· == 0)).reverse

def add : IntPolynomial → IntPolynomial → IntPolynomial
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x + y) :: add a b

def scale (k : Int) (p : IntPolynomial) : IntPolynomial := p.map (k * ·)

def mul : IntPolynomial → IntPolynomial → IntPolynomial
  | [], _ => []
  | x :: a, b => add (scale x b) (0 :: mul a b)

end IntPolynomial

end QLS7
