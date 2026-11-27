/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.IntervalSoundness
public import Mathlib.Data.Nat.Bitwise

/-!
# Real interpretation of algebraic certificates
-/

@[expose] public section
set_option maxHeartbeats 0

noncomputable section

namespace QLS7

private theorem foldl_mul_eq {α : Type*} (l : List α) (f : α → ℝ) (a : ℝ) :
    l.foldl (fun b i => b * f i) a = a * (l.map f).prod := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih => simp [ih, mul_assoc]

private theorem foldl_add_eq {α : Type*} (l : List α) (f : α → ℝ) (a : ℝ) :
    l.foldl (fun b i => b + f i) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih => simp [ih, add_assoc]

private theorem contains_foldl {α : Type*} {scale : ℤ} (l : List α)
    (f : Interval → α → Interval) (g : ℝ → α → ℝ)
    (h : ∀ i ∈ l, ∀ a x, Interval.Contains scale a x → Interval.Contains scale (f a i) (g x i))
    (a : Interval) (x : ℝ) (hx : Interval.Contains scale a x) :
    Interval.Contains scale (l.foldl f a) (l.foldl g x) := by
  induction l generalizing a x with
  | nil => exact hx
  | cons i l ih =>
    apply ih (fun j hj => h j (by simp [hj]))
    exact h i (by simp) a x hx

namespace AlgebraicData

def radValue (c : AlgebraicData) (x : ℝ) (i : ℕ) : ℝ :=
  let (d, p) := c.radicands[i]?.getD (0, [])
  IntPolynomial.eval p x / d

def monomialValue (c : AlgebraicData) (x : ℝ) (m : ℕ) : ℝ :=
  ((List.range c.radicalCount).map fun i =>
    if m.testBit i then Real.sqrt (c.radValue x i) else 1).prod

def elemValue (c : AlgebraicData) (x : ℝ) (e : RadicalElement) : ℝ :=
  (e.map fun (m, p) => IntPolynomial.eval p x / c.coordinateScale * c.monomialValue x m).sum

def coordValue (c : AlgebraicData) (x : ℝ) (a k : ℕ) : ℝ := c.elemValue x (c.coord a k)

def denominator (c : AlgebraicData) : ℝ :=
  ((List.range c.radicalCount).map fun i =>
    let (d, _) := c.radicands[i]?.getD (0, [])
    (d : ℝ)).prod

theorem contains_radValue (c : AlgebraicData) {x : ℝ}
    (hs : 0 < c.intervalScale) (hx : Interval.Contains c.intervalScale c.rootInterval x)
    (i : ℕ) (hd : 0 < (c.radicands[i]?.getD (0, [])).1) :
    Interval.Contains c.intervalScale (c.radBounds i) (c.radValue x i) := by
  exact Interval.contains_eval hs _ _ hd hx

theorem contains_monomialValue (c : AlgebraicData) {x : ℝ} (hs : 0 < c.intervalScale)
    (h : ∀ i ∈ List.range c.radicalCount, Interval.Contains c.intervalScale
      (c.sqrtIntervals[i]?.getD (0, 0)) (Real.sqrt (c.radValue x i))) (m : ℕ) :
    Interval.Contains c.intervalScale (c.monomialBound m) (c.monomialValue x m) := by
  let f i := if m.testBit i then Real.sqrt (c.radValue x i) else 1
  have hstep (i : ℕ) (hi : i ∈ List.range c.radicalCount) (a : Interval) (y : ℝ)
      (hy : Interval.Contains c.intervalScale a y) :
      Interval.Contains c.intervalScale
        (if m.testBit i then Interval.mul c.intervalScale a
          (c.sqrtIntervals[i]?.getD (0, 0)) else a) (y * f i) := by
    dsimp [f]
    split
    · exact Interval.contains_mul hs hy (h i hi)
    · simpa using hy
  have hp := contains_foldl (scale := c.intervalScale) (List.range c.radicalCount)
    (fun a i => if m.testBit i then Interval.mul c.intervalScale a
      (c.sqrtIntervals[i]?.getD (0, 0)) else a)
    (fun a i => a * f i) hstep
    (c.intervalScale, c.intervalScale) 1 (by simp [Interval.Contains])
  rw [foldl_mul_eq] at hp
  simpa [monomialBound, monomialValue, f] using hp

theorem contains_elemValue (c : AlgebraicData) {x : ℝ}
    (hs : 0 < c.intervalScale) (hc : 0 < c.coordinateScale)
    (hx : Interval.Contains c.intervalScale c.rootInterval x)
    (h : ∀ i ∈ List.range c.radicalCount, Interval.Contains c.intervalScale
      (c.sqrtIntervals[i]?.getD (0, 0)) (Real.sqrt (c.radValue x i))) (e : RadicalElement) :
    Interval.Contains c.intervalScale (c.elemBound e) (c.elemValue x e) := by
  have hp := contains_foldl (scale := c.intervalScale) e
    (fun a (m, p) => Interval.add a (Interval.mul c.intervalScale
      (Interval.eval c.intervalScale p c.coordinateScale c.rootInterval) (c.monomialBound m)))
    (fun a (m, p) => a + IntPolynomial.eval p x / c.coordinateScale * c.monomialValue x m)
    (fun i _ a y hy => Interval.contains_add hy (Interval.contains_mul hs
      (Interval.contains_eval hs i.2 c.coordinateScale hc hx) (c.contains_monomialValue hs h i.1)))
    (0, 0) 0 (by simp [Interval.Contains])
  simpa [elemBound, elemValue, foldl_add_eq] using hp

theorem eval_makeFactor (c : AlgebraicData) (x : ℝ) (m : ℕ) :
    IntPolynomial.eval (c.makeFactor m) x =
      ((List.range c.radicalCount).map fun i =>
        let (d, p) := c.radicands[i]?.getD (0, [])
        if m.testBit i then IntPolynomial.eval p x else (d : ℝ)).prod := by
  let f i := if m.testBit i then IntPolynomial.eval (c.radicands[i]?.getD (0, [])).2 x
    else ((c.radicands[i]?.getD (0, [])).1 : ℝ)
  have hf (l : List ℕ) (a : IntPolynomial) :
      IntPolynomial.eval (l.foldl (fun a i =>
        let (d, p) := c.radicands[i]?.getD (0, [])
        if m.testBit i then IntPolynomial.mul a p else IntPolynomial.scale d a) a) x =
      IntPolynomial.eval a x * (l.map f).prod := by
    induction l generalizing a with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldl_cons, ih, List.map_cons, List.prod_cons]
      dsimp [f]
      split <;> simp [IntPolynomial.eval_mul, IntPolynomial.eval_scale] <;> ring
  simpa [makeFactor, f] using hf (List.range c.radicalCount) [1]

theorem monomialValue_mul (c : AlgebraicData) (x : ℝ)
    (hd : ∀ i ∈ List.range c.radicalCount, 0 < (c.radicands[i]?.getD (0, [])).1)
    (hr : ∀ i ∈ List.range c.radicalCount, 0 ≤ c.radValue x i) (a b : ℕ) :
    c.denominator * c.monomialValue x a * c.monomialValue x b =
      IntPolynomial.eval (c.makeFactor (Nat.land a b)) x * c.monomialValue x (Nat.xor a b) := by
  rw [eval_makeFactor]
  unfold denominator monomialValue
  simp only [← List.prod_map_mul]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hs := Real.sq_sqrt (hr i hi)
  have hdi : ((c.radicands[i]?.getD (0, [])).1 : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (hd i hi)
  have he : ((c.radicands[i]?.getD (0, [])).1 : ℝ) *
      Real.sqrt (c.radValue x i) ^ 2 = IntPolynomial.eval (c.radicands[i]?.getD (0, [])).2 x := by
    rw [hs]
    dsimp [radValue]
    field_simp
  simp only [Nat.land_eq, Nat.xor_eq, Nat.testBit_land, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> simp
  nlinarith [he]

end AlgebraicData

end QLS7
