/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.AlgebraicSoundness

/-!
# Orthogonality from polynomial certificates
-/

@[expose] public section
set_option maxHeartbeats 0

noncomputable section

namespace QLS7

open scoped BigOperators

private theorem eval_foldl_sum {α : Type*} (x : ℝ) (l : List α)
    (F : IntPolynomial → α → IntPolynomial) (f : α → ℝ)
    (h : ∀ p t, IntPolynomial.eval (F p t) x = IntPolynomial.eval p x + f t)
    (p : IntPolynomial) :
    IntPolynomial.eval (l.foldl F p) x = IntPolynomial.eval p x + (l.map f).sum := by
  induction l generalizing p with
  | nil => simp
  | cons a l ih => simp [ih, h, add_assoc]

private theorem sum_list_sum {α ι : Type*} [Fintype ι] (l : List α) (f : ι → α → ℝ) :
    (∑ i, (l.map (f i)).sum) = (l.map fun a => ∑ i, f i a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

private theorem list_range_sum (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ k : Fin n, f k := by
  rw [Fin.sum_univ_def]
  change ((List.range n).map f).sum = ((List.finRange n).map (f ∘ Fin.val)).sum
  rw [← List.map_map]
  simp

private theorem sum_list_weighted {α ι : Type*} [Fintype ι]
    (l : List α) (f : ι → α → ℝ) (w : ι → ℝ) :
    (∑ i, (l.map (f i)).sum * w i) = (l.map fun a => ∑ i, f i a * w i).sum := by
  simp_rw [← List.sum_map_mul_right]
  exact sum_list_sum l _

namespace AlgebraicData

theorem eval_dotMask (c : AlgebraicData) (x : ℝ) (a b m : ℕ) :
    IntPolynomial.eval (c.dotMask a b m) x =
      ((List.range c.order).map fun k => ((c.coord a k).map fun s =>
        ((c.coord b k).map fun t => if Nat.xor s.1 t.1 == m then
          IntPolynomial.eval s.2 x * IntPolynomial.eval t.2 x *
            IntPolynomial.eval (c.factors[Nat.land s.1 t.1]?.getD []) x
        else 0).sum).sum).sum := by
  let term (s t : ℕ × IntPolynomial) := if Nat.xor s.1 t.1 == m then
    IntPolynomial.eval s.2 x * IntPolynomial.eval t.2 x *
      IntPolynomial.eval (c.factors[Nat.land s.1 t.1]?.getD []) x else 0
  let step (s t : ℕ × IntPolynomial) (p : IntPolynomial) :=
    if Nat.xor s.1 t.1 == m then IntPolynomial.add p
      (IntPolynomial.mul (IntPolynomial.mul s.2 t.2) (c.factors[Nat.land s.1 t.1]?.getD []))
    else p
  have hstep (s t : ℕ × IntPolynomial) (p : IntPolynomial) :
      IntPolynomial.eval (step s t p) x = IntPolynomial.eval p x + term s t := by
    dsimp [step, term]
    split <;> simp [IntPolynomial.eval_add, IntPolynomial.eval_mul]
  have hinner (k : ℕ) (s : ℕ × IntPolynomial) (p : IntPolynomial) :=
    eval_foldl_sum x (c.coord b k) (fun p t => step s t p) (term s) (fun p t => hstep s t p) p
  have hmiddle (k : ℕ) (p : IntPolynomial) :=
    eval_foldl_sum x (c.coord a k)
      (fun p s => (c.coord b k).foldl (fun p t => step s t p) p)
      (fun s => ((c.coord b k).map (term s)).sum) (fun p s => hinner k s p) p
  have houter := eval_foldl_sum x (List.range c.order)
    (fun p k => (c.coord a k).foldl (fun p s =>
      (c.coord b k).foldl (fun p t => step s t p) p) p)
    (fun k => ((c.coord a k).map fun s => ((c.coord b k).map (term s)).sum).sum)
    (fun p k => hmiddle k p) []
  simpa [dotMask, IntPolynomial.eval_trim, step, term] using houter

theorem denominator_pos (c : AlgebraicData)
    (hd : ∀ i ∈ List.range c.radicalCount, 0 < (c.radicands[i]?.getD (0, [])).1) :
    0 < c.denominator := by
  apply List.prod_pos
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
  change (0 : ℝ) < (((c.radicands[i]?.getD (0, [])).1 : ℤ) : ℝ)
  exact_mod_cast hd i hi

theorem elemValue_scale (c : AlgebraicData) (x : ℝ) (e : RadicalElement)
    (hc : c.coordinateScale ≠ 0) :
    (c.coordinateScale : ℝ) * c.elemValue x e =
      (e.map fun (m, p) => IntPolynomial.eval p x * c.monomialValue x m).sum := by
  unfold elemValue
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  rintro ⟨m, p⟩ _
  dsimp only
  have hc' : (c.coordinateScale : ℝ) ≠ 0 := by exact_mod_cast hc
  field_simp

theorem sum_mask_term (c : AlgebraicData) (x : ℝ)
    (hd : ∀ i ∈ List.range c.radicalCount, 0 < (c.radicands[i]?.getD (0, [])).1)
    (hr : ∀ i ∈ List.range c.radicalCount, 0 ≤ c.radValue x i)
    (hf : ∀ m : Fin (2 ^ c.radicalCount), IntPolynomial.trim (c.makeFactor m) =
      c.factors[m.val]?.getD []) (s t : ℕ × IntPolynomial)
    (hs : s.1 < 2 ^ c.radicalCount) (ht : t.1 < 2 ^ c.radicalCount) :
    (∑ m : Fin (2 ^ c.radicalCount),
      (if Nat.xor s.1 t.1 == m.val then IntPolynomial.eval s.2 x * IntPolynomial.eval t.2 x *
        IntPolynomial.eval (c.factors[Nat.land s.1 t.1]?.getD []) x else 0) * c.monomialValue x m) =
      c.denominator * (IntPolynomial.eval s.2 x * c.monomialValue x s.1) *
        (IntPolynomial.eval t.2 x * c.monomialValue x t.1) := by
  classical
  let u : Fin (2 ^ c.radicalCount) := ⟨Nat.xor s.1 t.1, Nat.xor_lt_two_pow hs ht⟩
  have hsum : (∑ m : Fin (2 ^ c.radicalCount),
      (if Nat.xor s.1 t.1 == m.val then IntPolynomial.eval s.2 x * IntPolynomial.eval t.2 x *
        IntPolynomial.eval (c.factors[Nat.land s.1 t.1]?.getD []) x else 0) * c.monomialValue x m) =
      IntPolynomial.eval s.2 x * IntPolynomial.eval t.2 x *
        IntPolynomial.eval (c.factors[Nat.land s.1 t.1]?.getD []) x *
          c.monomialValue x (Nat.xor s.1 t.1) := by
    rw [Finset.sum_eq_single u]
    · simp [u]
    · intro m _ hne
      have hne' : s.1 ^^^ t.1 ≠ m.val := by
        intro h
        apply hne
        exact Fin.ext h.symm
      simp [hne']
    · simp
  rw [hsum]
  have hab : Nat.land s.1 t.1 < 2 ^ c.radicalCount := lt_of_le_of_lt Nat.and_le_left hs
  have hfactor := congrArg (fun p => IntPolynomial.eval p x) (hf ⟨Nat.land s.1 t.1, hab⟩)
  simp only [IntPolynomial.eval_trim] at hfactor
  have hmul := c.monomialValue_mul x hd hr s.1 t.1
  rw [hfactor] at hmul
  calc
    _ = IntPolynomial.eval s.2 x * IntPolynomial.eval t.2 x *
      (IntPolynomial.eval (c.factors[Nat.land s.1 t.1]?.getD []) x *
        c.monomialValue x (Nat.xor s.1 t.1)) := by ring
    _ = _ := by rw [← hmul]; ring

theorem sum_mask_elements (c : AlgebraicData) (x : ℝ)
    (hd : ∀ i ∈ List.range c.radicalCount, 0 < (c.radicands[i]?.getD (0, [])).1)
    (hr : ∀ i ∈ List.range c.radicalCount, 0 ≤ c.radValue x i)
    (hf : ∀ m : Fin (2 ^ c.radicalCount), IntPolynomial.trim (c.makeFactor m) =
      c.factors[m.val]?.getD []) (hc : c.coordinateScale ≠ 0)
    (e f : RadicalElement) (he : ∀ s ∈ e, s.1 < 2 ^ c.radicalCount)
    (ht : ∀ t ∈ f, t.1 < 2 ^ c.radicalCount) :
    (∑ m : Fin (2 ^ c.radicalCount), (e.map fun s => (f.map fun t =>
      if Nat.xor s.1 t.1 == m.val then IntPolynomial.eval s.2 x * IntPolynomial.eval t.2 x *
        IntPolynomial.eval (c.factors[Nat.land s.1 t.1]?.getD []) x else 0).sum).sum *
          c.monomialValue x m) =
      (c.denominator * (c.coordinateScale : ℝ) ^ 2) * (c.elemValue x e * c.elemValue x f) := by
  simp_rw [← List.sum_map_mul_right, sum_list_sum]
  calc
    _ = (e.map fun s => (f.map fun t => c.denominator *
      (IntPolynomial.eval s.2 x * c.monomialValue x s.1) *
        (IntPolynomial.eval t.2 x * c.monomialValue x t.1)).sum).sum := by
      congr 1
      apply List.map_congr_left
      intro s hs
      congr 1
      apply List.map_congr_left
      intro t htf
      exact c.sum_mask_term x hd hr hf s t (he s hs) (ht t htf)
    _ = _ := by
      simp only [List.sum_map_mul_left, List.sum_map_mul_right]
      rw [← c.elemValue_scale x e hc, ← c.elemValue_scale x f hc]
      ring

theorem sum_mask_dot (c : AlgebraicData) (x : ℝ)
    (hd : ∀ i ∈ List.range c.radicalCount, 0 < (c.radicands[i]?.getD (0, [])).1)
    (hr : ∀ i ∈ List.range c.radicalCount, 0 ≤ c.radValue x i)
    (hf : ∀ m : Fin (2 ^ c.radicalCount), IntPolynomial.trim (c.makeFactor m) =
      c.factors[m.val]?.getD []) (hc : c.coordinateScale ≠ 0) (a b : ℕ)
    (ha : ∀ k ∈ List.range c.order, ∀ s ∈ c.coord a k, s.1 < 2 ^ c.radicalCount)
    (hb : ∀ k ∈ List.range c.order, ∀ s ∈ c.coord b k, s.1 < 2 ^ c.radicalCount) :
    (∑ m : Fin (2 ^ c.radicalCount), IntPolynomial.eval (c.dotMask a b m) x * c.monomialValue x m) =
      (c.denominator * (c.coordinateScale : ℝ) ^ 2) *
        ∑ k : Fin c.order, c.coordValue x a k * c.coordValue x b k := by
  simp_rw [eval_dotMask]
  rw [sum_list_weighted]
  calc
    _ = ((List.range c.order).map fun k =>
      (c.denominator * (c.coordinateScale : ℝ) ^ 2) *
        (c.elemValue x (c.coord a k) * c.elemValue x (c.coord b k))).sum := by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact c.sum_mask_elements x hd hr hf hc _ _ (ha k hk) (hb k hk)
    _ = _ := by rw [List.sum_map_mul_left, list_range_sum]; rfl

theorem dot_eq_zero (c : AlgebraicData) (x : ℝ)
    (hd : ∀ i ∈ List.range c.radicalCount, 0 < (c.radicands[i]?.getD (0, [])).1)
    (hr : ∀ i ∈ List.range c.radicalCount, 0 ≤ c.radValue x i)
    (hf : ∀ m : Fin (2 ^ c.radicalCount), IntPolynomial.trim (c.makeFactor m) =
      c.factors[m.val]?.getD []) (hc : c.coordinateScale ≠ 0) (a b : ℕ)
    (ha : ∀ k ∈ List.range c.order, ∀ s ∈ c.coord a k, s.1 < 2 ^ c.radicalCount)
    (hb : ∀ k ∈ List.range c.order, ∀ s ∈ c.coord b k, s.1 < 2 ^ c.radicalCount)
    (horth : ∀ m : Fin (2 ^ c.radicalCount), IntPolynomial.eval (c.dotMask a b m) x = 0) :
    ∑ k : Fin c.order, c.coordValue x a k * c.coordValue x b k = 0 := by
  have h := c.sum_mask_dot x hd hr hf hc a b ha hb
  simp only [horth, zero_mul, Finset.sum_const_zero] at h
  have hc' : (c.coordinateScale : ℝ) ≠ 0 := by exact_mod_cast hc
  exact (mul_eq_zero.mp h.symm).resolve_left
    (mul_ne_zero (ne_of_gt (c.denominator_pos hd)) (pow_ne_zero _ hc'))

end AlgebraicData

end QLS7
