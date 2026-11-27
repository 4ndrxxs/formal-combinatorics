/-
Copyright (c) 2026 Yuankai Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuankai Guo
Local adaptation: import paths and the elaboration heartbeat limit for Lean 4.36.
-/
module

public import Quantum.SmallSevenGuo.Certificate.Algebraic
public import Quantum.SmallSevenGuo.Certificate.PolynomialSoundness

/-!
# Soundness of rational interval arithmetic

An interval with integer endpoints and positive scale contains `x` when its endpoints
bound `scale * x`. Integer division rounds the lower endpoint down and the upper endpoint up.
-/

@[expose] public section
set_option maxHeartbeats 0

noncomputable section

namespace QLS7.Interval

def Contains (scale : ℤ) (a : Interval) (x : ℝ) : Prop :=
  (a.1 : ℝ) ≤ scale * x ∧ scale * x ≤ a.2

theorem floorDiv_le (a b : ℤ) (hb : 0 < b) :
    ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  apply (le_div_iff₀ (by exact_mod_cast hb)).2
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)

theorem le_ceilDiv (a b : ℤ) (hb : 0 < b) :
    (a : ℝ) / b ≤ (ceilDiv a b : ℝ) := by
  simpa [ceilDiv, neg_div] using neg_le_neg (floorDiv_le (-a) b hb)

theorem contains_const (scale n d : ℤ) (hd : 0 < d) :
    Contains scale (const scale n d) ((n : ℝ) / d) := by
  unfold Contains const
  constructor
  · convert floorDiv_le (n * scale) d hd using 1
    push_cast
    ring
  · convert le_ceilDiv (n * scale) d hd using 1
    push_cast
    ring

theorem contains_add {scale : ℤ} {a b : Interval} {x y : ℝ}
    (hx : Contains scale a x) (hy : Contains scale b y) :
    Contains scale (add a b) (x + y) := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  constructor <;> dsimp [add] <;> push_cast <;> nlinarith

private theorem mul_bounds {a b c d x y l u : ℝ}
    (hx0 : a ≤ x) (hx1 : x ≤ b) (hy0 : c ≤ y) (hy1 : y ≤ d)
    (hl0 : l ≤ a * c) (hl1 : l ≤ a * d) (hl2 : l ≤ b * c) (hl3 : l ≤ b * d)
    (hu0 : a * c ≤ u) (hu1 : a * d ≤ u) (hu2 : b * c ≤ u) (hu3 : b * d ≤ u) :
    l ≤ x * y ∧ x * y ≤ u := by
  constructor
  · rcases le_total 0 y with hy | hy
    · apply le_trans _ (mul_le_mul_of_nonneg_right hx0 hy)
      rcases le_total 0 a with ha | ha
      · exact hl0.trans (mul_le_mul_of_nonneg_left hy0 ha)
      · exact hl1.trans (mul_le_mul_of_nonpos_left hy1 ha)
    · apply le_trans _ (mul_le_mul_of_nonpos_right hx1 hy)
      rcases le_total 0 b with hb | hb
      · exact hl2.trans (mul_le_mul_of_nonneg_left hy0 hb)
      · exact hl3.trans (mul_le_mul_of_nonpos_left hy1 hb)
  · rcases le_total 0 y with hy | hy
    · apply le_trans (mul_le_mul_of_nonneg_right hx1 hy)
      rcases le_total 0 b with hb | hb
      · exact (mul_le_mul_of_nonneg_left hy1 hb).trans hu3
      · exact (mul_le_mul_of_nonpos_left hy0 hb).trans hu2
    · apply le_trans (mul_le_mul_of_nonpos_right hx0 hy)
      rcases le_total 0 a with ha | ha
      · exact (mul_le_mul_of_nonneg_left hy1 ha).trans hu1
      · exact (mul_le_mul_of_nonpos_left hy0 ha).trans hu0

theorem contains_mul {scale : ℤ} (hs : 0 < scale) {a b : Interval} {x y : ℝ}
    (hx : Contains scale a x) (hy : Contains scale b y) :
    Contains scale (mul scale a b) (x * y) := by
  let l := min (min (min (a.1 * b.1) (a.1 * b.2)) (a.2 * b.1)) (a.2 * b.2)
  let u := max (max (max (a.1 * b.1) (a.1 * b.2)) (a.2 * b.1)) (a.2 * b.2)
  have hb : (l : ℝ) ≤ ((scale : ℝ) * x) * (scale * y) ∧
      ((scale : ℝ) * x) * (scale * y) ≤ u := by
    apply mul_bounds hx.1 hx.2 hy.1 hy.2
    all_goals norm_cast
    all_goals simp [l, u, min_le_iff, le_max_iff]
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  simp only [Contains, mul, List.foldl, min_self, max_self]
  change ((l / scale : ℤ) : ℝ) ≤ (scale : ℝ) * (x * y) ∧
    (scale : ℝ) * (x * y) ≤ (ceilDiv u scale : ℝ)
  constructor
  · apply (floorDiv_le l scale hs).trans
    apply (div_le_iff₀ hs').2
    convert hb.1 using 1
    ring
  · apply le_trans _ (le_ceilDiv u scale hs)
    apply (le_div_iff₀ hs').2
    convert hb.2 using 1
    ring

theorem contains_eval {scale : ℤ} (hs : 0 < scale) (p : IntPolynomial)
    (d : ℤ) (hd : 0 < d) {a : Interval} {x : ℝ} (hx : Contains scale a x) :
    Contains scale (eval scale p d a) (IntPolynomial.eval p x / d) := by
  induction p with
  | nil => simp [eval, Contains]
  | cons c p ih =>
    have h := contains_add (contains_mul hs ih hx) (contains_const scale c d hd)
    convert h using 1 <;> simp [eval, IntPolynomial.eval_cons]
    ring

theorem contains_mono {scale : ℤ} {a b : Interval} {x : ℝ}
    (hx : Contains scale a x) (h0 : b.1 ≤ a.1) (h1 : a.2 ≤ b.2) :
    Contains scale b x := by
  constructor
  · exact le_trans (by exact_mod_cast h0) hx.1
  · exact le_trans hx.2 (by exact_mod_cast h1)

theorem contains_sub {scale : ℤ} {a b : Interval} {x y : ℝ}
    (hx : Contains scale a x) (hy : Contains scale b y) :
    Contains scale (a.1 - b.2, a.2 - b.1) (x - y) := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  constructor <;> dsimp <;> push_cast <;> nlinarith

theorem contains_sqrt {scale : ℤ} (hs : 0 < scale) {a b : Interval} {x : ℝ}
    (hx : Contains scale a x) (ha : 0 < a.1) (hb0 : 0 < b.1) (hb1 : b.1 ≤ b.2)
    (hlo : b.1 * b.1 ≤ a.1 * scale) (hhi : a.2 * scale ≤ b.2 * b.2) :
    Contains scale b (Real.sqrt x) := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  have ha' : (0 : ℝ) < a.1 := by exact_mod_cast ha
  have hxpos : 0 ≤ x := by nlinarith [hx.1]
  have hsq := Real.sq_sqrt hxpos
  have hn := Real.sqrt_nonneg x
  have hb0' : (0 : ℝ) < b.1 := by exact_mod_cast hb0
  have hb1' : (b.1 : ℝ) ≤ b.2 := by exact_mod_cast hb1
  have hlo' : (b.1 : ℝ) * b.1 ≤ (a.1 : ℝ) * scale := by exact_mod_cast hlo
  have hhi' : (a.2 : ℝ) * scale ≤ (b.2 : ℝ) * b.2 := by exact_mod_cast hhi
  have hlo'' := mul_le_mul_of_nonneg_right hx.1 hs'.le
  have hhi'' := mul_le_mul_of_nonneg_right hx.2 hs'.le
  have hsqs : ((scale : ℝ) * Real.sqrt x) ^ 2 = (scale : ℝ) * x * scale := by
    rw [mul_pow, hsq]
    ring
  have hnonneg : 0 ≤ (scale : ℝ) * Real.sqrt x := mul_nonneg hs'.le hn
  constructor <;> nlinarith

theorem contains_iff {scale : ℤ} (hs : 0 < scale) (a : Interval) (x : ℝ) :
    Contains scale a x ↔ x ∈ Set.Icc ((a.1 : ℝ) / scale) ((a.2 : ℝ) / scale) := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  simp only [Contains, Set.mem_Icc, div_le_iff₀ hs', le_div_iff₀ hs', mul_comm]

theorem contains_point {scale : ℤ} (hs : 0 < scale) (a : ℤ) :
    Contains scale (a, a) ((a : ℝ) / scale) := by
  rw [contains_iff hs]
  exact ⟨le_rfl, le_rfl⟩

theorem positive_of_contains {scale : ℤ} (hs : 0 < scale) {a : Interval} {x : ℝ}
    (hx : Contains scale a x) (ha : 0 < a.1) : 0 < x := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  have ha' : (0 : ℝ) < a.1 := by exact_mod_cast ha
  nlinarith [hx.1]

theorem negative_of_contains {scale : ℤ} (hs : 0 < scale) {a : Interval} {x : ℝ}
    (hx : Contains scale a x) (ha : a.2 < 0) : x < 0 := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  have ha' : (a.2 : ℝ) < 0 := by exact_mod_cast ha
  nlinarith [hx.2]

theorem exists_root {scale : ℤ} (hs : 0 < scale) (p : IntPolynomial) (a : Interval)
    (ha : a.1 < a.2)
    (hsign :
      ((eval scale p 1 (a.1, a.1)).2 < 0 ∧ 0 < (eval scale p 1 (a.2, a.2)).1) ∨
      (0 < (eval scale p 1 (a.1, a.1)).1 ∧ (eval scale p 1 (a.2, a.2)).2 < 0)) :
    ∃ x, Contains scale a x ∧ IntPolynomial.eval p x = 0 := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  have hab : (a.1 : ℝ) / scale ≤ (a.2 : ℝ) / scale :=
    (div_le_div_iff_of_pos_right hs').2 (by exact_mod_cast ha.le)
  have h0 := contains_eval hs p 1 (by decide) (contains_point hs a.1)
  have h1 := contains_eval hs p 1 (by decide) (contains_point hs a.2)
  simp only [Int.cast_one, div_one] at h0 h1
  have hc : ContinuousOn (IntPolynomial.eval p)
      (Set.Icc ((a.1 : ℝ) / scale) ((a.2 : ℝ) / scale)) :=
    (IntPolynomial.continuous_eval p).continuousOn
  have hr : 0 ∈ IntPolynomial.eval p ''
      Set.Icc ((a.1 : ℝ) / scale) ((a.2 : ℝ) / scale) := by
    rcases hsign with h | h
    · exact intermediate_value_Icc hab hc
        ⟨(negative_of_contains hs h0 h.1).le, (positive_of_contains hs h1 h.2).le⟩
    · exact intermediate_value_Icc' hab hc
        ⟨(negative_of_contains hs h1 h.2).le, (positive_of_contains hs h0 h.1).le⟩
  obtain ⟨x, hx, hp⟩ := hr
  exact ⟨x, (contains_iff hs a x).2 hx, hp⟩

end QLS7.Interval
