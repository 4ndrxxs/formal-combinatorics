/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.Polynomial

/-!
# Algebraic certificates

Coordinates are sums of polynomials times square-root monomials, indexed by bit masks.
Intervals have integer endpoints with a common denominator. All interval operations round
outwards; the certificates check the resulting integer inequalities.
-/

@[expose] public section
set_option maxHeartbeats 0

namespace QLS7

/-- A sparse sum of polynomial multiples of square-root monomials. -/
abbrev RadicalElement := List (Nat × IntPolynomial)

/-- Integer endpoints of an interval with a separately specified positive denominator. -/
abbrev Interval := Int × Int

namespace Interval

def ceilDiv (a b : Int) : Int := -((-a) / b)

def const (scale n d : Int) : Interval :=
  (n * scale / d, ceilDiv (n * scale) d)

def add (a b : Interval) : Interval := (a.1 + b.1, a.2 + b.2)

def mul (scale : Int) (a b : Interval) : Interval :=
  let p := [a.1 * b.1, a.1 * b.2, a.2 * b.1, a.2 * b.2]
  (p.foldl min (a.1 * b.1) / scale, ceilDiv (p.foldl max (a.1 * b.1)) scale)

def eval (scale : Int) (p : IntPolynomial) (d : Int) (x : Interval) : Interval :=
  p.foldr (fun c acc => add (mul scale acc x) (const scale c d)) (0, 0)

end Interval

/-- Data used in the polynomial and interval checks for an algebraic construction. -/
structure AlgebraicData where
  order : Nat
  cardinality : Nat
  radicalCount : Nat
  coordinateScale : Int
  intervalScale : Int
  radicands : List (Int × IntPolynomial)
  factors : List IntPolynomial
  grid : List (List Nat)
  rays : List (List RadicalElement)
  rootInterval : Interval
  sqrtIntervals : List Interval
  coordinateBounds : List (List Interval)

namespace AlgebraicData

def makeFactor (c : AlgebraicData) (m : Nat) : IntPolynomial :=
  (List.range c.radicalCount).foldl (fun a i =>
    let (d, p) := c.radicands[i]?.getD (0, [])
    if m.testBit i then IntPolynomial.mul a p else IntPolynomial.scale d a) [1]

def coord (c : AlgebraicData) (a k : Nat) : RadicalElement :=
  (c.rays[a]?.getD [])[k]?.getD []

def label (c : AlgebraicData) (i j : Nat) : Nat :=
  (c.grid[i]?.getD [])[j]?.getD c.cardinality

def dotMask (c : AlgebraicData) (a b m : Nat) : IntPolynomial :=
  IntPolynomial.trim <| (List.range c.order).foldl (fun total k =>
    (c.coord a k).foldl (fun acc (i, p) =>
      (c.coord b k).foldl (fun acc' (j, q) =>
        if Nat.xor i j == m then
          IntPolynomial.add acc' (IntPolynomial.mul (IntPolynomial.mul p q)
            (c.factors[Nat.land i j]?.getD []))
        else acc') acc) total) []

def lines (c : AlgebraicData) : List (List Nat) :=
  c.grid ++ (List.range c.order).map (fun j => (List.range c.order).map (fun i => c.label i j))

def orthPairs (c : AlgebraicData) : List (Nat × Nat) :=
  c.lines.flatMap fun line =>
    (List.range c.order).flatMap fun i =>
      ((List.range c.order).filter (i < ·)).map fun j =>
        (line[i]?.getD c.cardinality, line[j]?.getD c.cardinality)

def radBounds (c : AlgebraicData) (i : Nat) : Interval :=
  let (d, p) := c.radicands[i]?.getD (0, [])
  Interval.eval c.intervalScale p d c.rootInterval

def monomialBound (c : AlgebraicData) (m : Nat) : Interval :=
  (List.range c.radicalCount).foldl (fun acc i =>
    if m.testBit i then Interval.mul c.intervalScale acc (c.sqrtIntervals[i]?.getD (0, 0))
    else acc) (c.intervalScale, c.intervalScale)

def elemBound (c : AlgebraicData) (e : RadicalElement) : Interval :=
  e.foldl (fun acc (m, p) => Interval.add acc
    (Interval.mul c.intervalScale (Interval.eval c.intervalScale p c.coordinateScale c.rootInterval)
      (c.monomialBound m))) (0, 0)

def bound (c : AlgebraicData) (a k : Nat) : Interval :=
  (c.coordinateBounds[a]?.getD [])[k]?.getD (0, 0)

def minorBound (c : AlgebraicData) (a b k l : Nat) : Interval :=
  let x := Interval.mul c.intervalScale (c.bound a k) (c.bound b l)
  let y := Interval.mul c.intervalScale (c.bound a l) (c.bound b k)
  (x.1 - y.2, x.2 - y.1)

def separationOK (c : AlgebraicData) (t : Nat × Nat × Nat × Nat) : Bool :=
  let (a, b, k, l) := t
  let v := c.minorBound a b k l
  a < b && b < c.cardinality && k < l && l < c.order &&
    (v.1 > c.intervalScale / 100000000 || v.2 < -(c.intervalScale / 100000000))

def allRayPairs (c : AlgebraicData) : List (Nat × Nat) :=
  (List.range c.cardinality).flatMap fun a =>
    ((List.range c.cardinality).filter (a < ·)).map fun b => (a, b)

def multiplicity (c : AlgebraicData) (a : Nat) : Nat := c.grid.flatten.count a

end AlgebraicData

end QLS7
