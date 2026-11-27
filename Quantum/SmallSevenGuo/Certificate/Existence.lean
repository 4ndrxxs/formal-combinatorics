/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.OrthogonalitySoundness

/-!
# Quantum Latin squares from algebraic certificates
-/

@[expose] public section
set_option maxHeartbeats 0

noncomputable section

namespace QLS7.AlgebraicData

theorem exists_quantumLatinSquare (c : AlgebraicData) (x : ℝ)
    (hcard : 2 ≤ c.cardinality) (hs : 0 < c.intervalScale) (hc : 0 < c.coordinateScale)
    (hx : Interval.Contains c.intervalScale c.rootInterval x)
    (hd : ∀ i : Fin c.radicalCount, 0 < (c.radicands[i.val]?.getD (0, [])).1)
    (hf : ∀ m : Fin (2 ^ c.radicalCount), IntPolynomial.trim (c.makeFactor m) =
      c.factors[m.val]?.getD [])
    (hsqrt : ∀ i : Fin c.radicalCount,
      let b := c.radBounds i
      let s := c.sqrtIntervals[i.val]?.getD (0, 0)
      0 < b.1 ∧ b.1 ≤ b.2 ∧ 0 < s.1 ∧ s.1 ≤ s.2 ∧
      s.1 * s.1 ≤ b.1 * c.intervalScale ∧ s.2 * s.2 ≥ b.2 * c.intervalScale)
    (hmask : ∀ a : Fin c.cardinality, ∀ k : Fin c.order,
      (c.coord a k).all (fun t => t.1 < 2 ^ c.radicalCount) = true)
    (hbound : ∀ a : Fin c.cardinality, ∀ k : Fin c.order,
      let b := c.elemBound (c.coord a k)
      let d := c.bound a k
      d.1 ≤ b.1 ∧ b.2 ≤ d.2)
    (hsep : ∀ a b : Fin c.cardinality, a ≠ b → ∃ k l : Fin c.order,
      0 < (c.minorBound a b k l).1 ∨ (c.minorBound a b k l).2 < 0)
    (hlabel : ∀ i j : Fin c.order, c.label i j < c.cardinality)
    (hrow : ∀ i j k : Fin c.order, j < k → ∀ m : Fin (2 ^ c.radicalCount),
      IntPolynomial.eval (c.dotMask (c.label i j) (c.label i k) m) x = 0)
    (hcol : ∀ j i k : Fin c.order, i < k → ∀ m : Fin (2 ^ c.radicalCount),
      IntPolynomial.eval (c.dotMask (c.label i j) (c.label k j) m) x = 0)
    (hcover : ∀ a : Fin c.cardinality, ∃ i j : Fin c.order, c.label i j = a) :
    ∃ q : QuantumLatinSquare c.order, q.cardinality = c.cardinality := by
  have hd' (i : ℕ) (hi : i ∈ List.range c.radicalCount) := hd ⟨i, List.mem_range.mp hi⟩
  have hr (i : ℕ) (hi : i ∈ List.range c.radicalCount) : 0 ≤ c.radValue x i := by
    exact (Interval.positive_of_contains hs (c.contains_radValue hs hx i (hd' i hi))
      (hsqrt ⟨i, List.mem_range.mp hi⟩).1).le
  have hsqrt' (i : ℕ) (hi : i ∈ List.range c.radicalCount) :
      Interval.Contains c.intervalScale (c.sqrtIntervals[i]?.getD (0, 0))
        (Real.sqrt (c.radValue x i)) := by
    obtain ⟨hb0, _, hs0, hs1, hlo, hhi⟩ := hsqrt ⟨i, List.mem_range.mp hi⟩
    exact Interval.contains_sqrt hs (c.contains_radValue hs hx i (hd' i hi)) hb0 hs0 hs1 hlo hhi
  have hcoords (a : Fin c.cardinality) (k : Fin c.order) :
      Interval.Contains c.intervalScale (c.bound a k) (c.coordValue x a k) :=
    Interval.contains_mono (c.contains_elemValue hs hc hx hsqrt' (c.coord a k))
      (hbound a k).1 (hbound a k).2
  have hminors (a b : Fin c.cardinality) (k l : Fin c.order) :
      Interval.Contains c.intervalScale (c.minorBound a b k l)
        (c.coordValue x a k * c.coordValue x b l - c.coordValue x a l * c.coordValue x b k) :=
    Interval.contains_sub (Interval.contains_mul hs (hcoords a k) (hcoords b l))
      (Interval.contains_mul hs (hcoords a l) (hcoords b k))
  have hdistinct (a b : Fin c.cardinality) (hab : a ≠ b) : ∃ k l : Fin c.order,
      c.coordValue x a k * c.coordValue x b l ≠ c.coordValue x a l * c.coordValue x b k := by
    obtain ⟨k, l, hkl⟩ := hsep a b hab
    refine ⟨k, l, ?_⟩
    intro heq
    rcases hkl with hkl | hkl
    · exact (ne_of_gt (Interval.positive_of_contains hs (hminors a b k l) hkl))
        (sub_eq_zero.mpr heq)
    · exact (ne_of_lt (Interval.negative_of_contains hs (hminors a b k l) hkl))
        (sub_eq_zero.mpr heq)
  have : Nontrivial (Fin c.cardinality) := Fin.nontrivial_iff_two_le.mpr hcard
  have hv (a : Fin c.cardinality) : ∃ k : Fin c.order, c.coordValue x a k ≠ 0 := by
    obtain ⟨b, hba⟩ := exists_ne a
    obtain ⟨k, l, hkl⟩ := hdistinct a b hba.symm
    by_contra h
    push Not at h
    exact hkl (by simp [h])
  have hm (a : Fin c.cardinality) : ∀ k ∈ List.range c.order,
      ∀ t ∈ c.coord a k, t.1 < 2 ^ c.radicalCount := by
    intro k hk t ht
    exact of_decide_eq_true (List.all_eq_true.mp (hmask a ⟨k, List.mem_range.mp hk⟩) t ht)
  let labels (i j : Fin c.order) : Fin c.cardinality := ⟨c.label i j, hlabel i j⟩
  apply QuantumLatinSquare.exists_of_real_coordinates (fun a k => c.coordValue x a k) hv labels
  · intro i j k hjk
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · exact c.dot_eq_zero x hd' hr hf hc.ne' _ _ (hm (labels i j)) (hm (labels i k))
        (hrow i j k hjk)
    · have h := c.dot_eq_zero x hd' hr hf hc.ne' _ _ (hm (labels i k)) (hm (labels i j))
        (hrow i k j hkj)
      simpa [mul_comm] using h
  · intro j i k hik
    rcases lt_or_gt_of_ne hik with hik | hki
    · exact c.dot_eq_zero x hd' hr hf hc.ne' _ _ (hm (labels i j)) (hm (labels k j))
        (hcol j i k hik)
    · have h := c.dot_eq_zero x hd' hr hf hc.ne' _ _ (hm (labels k j)) (hm (labels i j))
        (hcol j k i hki)
      simpa [mul_comm] using h
  · exact hdistinct
  · intro a
    obtain ⟨i, j, h⟩ := hcover a
    exact ⟨i, j, Fin.ext h⟩

end QLS7.AlgebraicData
