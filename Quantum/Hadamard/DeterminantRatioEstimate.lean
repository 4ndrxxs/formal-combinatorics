import Mathlib

/-! A lower estimate for the determinant of an Ehlich–Wojtas Gram block from the
first two moments and a one-sided bound on its normalized eigenvalue deviations. -/

open scoped BigOperators
open Real Set

namespace Hadamard.DeterminantRatio

private theorem log_remainder_pos {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.log (1 + x) - x + x ^ 2 / 2 := by
  let f : ℝ → ℝ := fun t ↦ Real.log (1 + t) - t + t ^ 2 / 2
  have df (t : ℝ) (ht : 0 ≤ t) : HasDerivAt f (t^2 / (1 + t)) t := by
    have hn : 1 + t ≠ 0 := by linarith
    convert ((((hasDerivAt_id t).const_add (1 : ℝ)).log hn).sub
      (hasDerivAt_id t) |>.add ((hasDerivAt_pow 2 t).div_const 2)) using 1 <;>
      first | rfl | (dsimp [f, Function.comp_def]; field_simp; ring)
  have mono : MonotoneOn f (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t ht ↦ (df t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (df t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ by have h : 0 ≤ t := interior_subset ht; positivity)
  simpa [f] using mono (show (0 : ℝ) ∈ Ici 0 by simp) hx hx

private theorem log_remainder_neg {x : ℝ} (hx : -(1 : ℝ) / 13 ≤ x) (h0 : x ≤ 0) :
    0 ≤ Real.log (1 + x) - x + x ^ 2 / 2 - 13 * x ^ 3 / 36 := by
  let f : ℝ → ℝ := fun t ↦ Real.log (1 + t) - t + t ^ 2 / 2 - 13 * t ^ 3 / 36
  have df (t : ℝ) (ht : -(1 : ℝ) / 13 ≤ t) :
      HasDerivAt f (-(t^2 * (1+13*t)) / (12*(1+t))) t := by
    have hn : 1 + t ≠ 0 := by linarith
    convert (((((hasDerivAt_id t).const_add (1 : ℝ)).log hn).sub
      (hasDerivAt_id t) |>.add ((hasDerivAt_pow 2 t).div_const 2)).sub
      (((hasDerivAt_pow 3 t).const_mul 13).div_const 36)) using 1 <;>
      first | rfl | (dsimp [f, Function.comp_def]; field_simp; ring)
  have anti : AntitoneOn f (Ici (-(1 : ℝ) / 13)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
      (fun t ht ↦ (df t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (df t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ by
        have h : -(1 : ℝ) / 13 ≤ t := interior_subset ht
        apply div_nonpos_of_nonpos_of_nonneg
        · exact neg_nonpos.mpr (mul_nonneg (sq_nonneg _) (by linarith))
        · linarith)
  simpa [f] using anti hx (show (-(1:ℝ) / 13) ≤ 0 by norm_num) h0

/-- The logarithmic quadratic minorant needs no upper bound on `x`. -/
theorem log_one_add_lower {x : ℝ} (hx : -(1 : ℝ) / 13 ≤ x) :
    x - 19 / 36 * x^2 ≤ Real.log (1 + x) := by
  rcases le_total 0 x with h | h
  · nlinarith [log_remainder_pos h, sq_nonneg x]
  · have hprod := mul_nonneg (sq_nonneg x) (show 0 ≤ 1 + 13*x by linarith)
    nlinarith [log_remainder_neg hx h]

private theorem log_eight_fifths : Real.log ((8 : ℝ)/5) ≤ 17/36 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 + 17/(36*128))
    (by simpa [add_comm] using Real.add_one_le_exp ((17:ℝ)/(36*128))) 128
  have he : Real.exp ((17:ℝ)/(36*128)) ^ 128 = Real.exp (17/36) := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc
    (8:ℝ) / 5 ≤ (1 + 17/(36*128)) ^ 128 := by norm_num
    _ ≤ _ := h.trans_eq he

/-- A lower bound for the product of normalized eigenvalues of one Gram block. -/
theorem normalized_four_fifths {I : Type*} [Fintype I] (k : ℕ) (hk : 0 < k) (x : I → ℝ)
    (mean : ∑ i, x i = 0) (moment : ∑ i, x i ^ 2 ≤ 1 - 1 / ((k:ℝ) + 1))
    (lo : ∀ i, -(1 : ℝ) / 13 ≤ x i) :
    (8/5:ℝ) * (1 - 1/(2*((k:ℝ)+1))) * (1 - 1/((k:ℝ)+1))^k ≤ ∏ i, (1+x i) := by
  have kr : 0 < (k:ℝ) := by exact_mod_cast hk
  have ka : 0 < (k:ℝ) + 1 := by linarith
  have pa : 0 < 1 - 1/(2*((k:ℝ)+1)) := sub_pos.mpr ((div_lt_one (by positivity)).mpr (by linarith))
  have pb : 0 < 1 - 1/((k:ℝ)+1) := sub_pos.mpr ((div_lt_one ka).mpr (by linarith))
  have pc (i : I) : 0 < 1 + x i := by linarith [lo i]
  have sum_le := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ log_one_add_lower (lo i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, mean, zero_sub] at sum_le
  apply (Real.log_le_log_iff (by positivity) (Finset.prod_pos fun i _ ↦ pc i)).mp
  rw [Real.log_mul (mul_ne_zero (by norm_num) pa.ne') (pow_ne_zero _ pb.ne'),
    Real.log_mul (by norm_num) pa.ne', Real.log_pow, Real.log_prod (fun i _ ↦ (pc i).ne')]
  calc
    _ ≤ 17/36 - 1/(2*((k:ℝ)+1)) - k*(1/((k:ℝ)+1)) := by
      linarith [log_eight_fifths, Real.log_le_sub_one_of_pos pa,
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos pb) kr.le]
    _ ≤ -(19/36:ℝ) * (1 - 1 / ((k:ℝ) + 1)) := by field_simp; linarith
    _ ≤ _ := by linarith

/-- Four fifths of the Ehlich–Wojtas expression for a block of dimension `k+1`,
with common Gram diagonal `2*(k+1)`. The eigenvalues are `2*(k+1)*(1+x i)`. -/
theorem four_fifths_of_moments {I : Type*} [Fintype I] (k : ℕ) (hk : 0 < k)
    (card : Fintype.card I = k+1) (x : I → ℝ) (mean : ∑ i, x i = 0)
    (moment : ∑ i, x i ^ 2 ≤ 1 - 1 / ((k:ℝ) + 1))
    (lo : ∀ i, -(1 : ℝ) / 13 ≤ x i) :
    (4/5:ℝ) * (2 * (2*((k:ℝ)+1)) - 2) * (2*((k:ℝ)+1)-2)^k ≤
      ∏ i, (2*((k:ℝ)+1) * (1+x i)) := by
  let v : ℝ := (k:ℝ) + 1
  let n : ℝ := 2*v
  have vp : 0 < v := by dsimp [v]; positivity
  have np : 0 < n := by dsimp [n]; positivity
  have eq1 : n*(1-1/n) = n-1 := by field_simp
  have eq2 : n*(1-1/v) = n-2 := by dsimp [n]; field_simp
  change (4/5:ℝ)*(2*n-2)*(n-2)^k ≤ ∏ i, (n*(1+x i))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card]
  calc
    _ = n^(k+1)*((8/5:ℝ)*(1-1/n)*(1-1/v)^k) := by
      rw [show 2*n-2 = 2*(n-1) by ring, ← eq1, ← eq2, mul_pow, pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (normalized_four_fifths k hk x mean moment lo) (by positivity)

/-- The same determinant bound from unscaled eigenvalue deviations. The moment
`4*k*(k+1)` is the sum of squares of the entries of a symmetric block having
zero diagonal and off-diagonal entries of absolute value two. -/
theorem four_fifths_gram_block {I : Type*} [Fintype I] (k : ℕ) (hk : 0 < k)
    (card : Fintype.card I = k+1) (e : I → ℝ) (mean : ∑ i, e i = 0)
    (moment : ∑ i, e i^2 ≤ 4*(k:ℝ)*((k:ℝ)+1))
    (lo : ∀ i, -(2*((k:ℝ)+1))/13 ≤ e i) :
    (4/5:ℝ) * (2 * (2*((k:ℝ)+1)) - 2) * (2*((k:ℝ)+1)-2)^k ≤
      ∏ i, (2*((k:ℝ)+1) + e i) := by
  let n : ℝ := 2*((k:ℝ)+1)
  have np : 0 < n := by dsimp [n]; positivity
  have M : ∑ i, e i/n = 0 := by rw [← Finset.sum_div, mean, zero_div]
  have V : ∑ i, (e i/n)^2 ≤ 1-1/((k:ℝ)+1) := by
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos np)).mpr
    calc
      _ ≤ 4*(k:ℝ)*((k:ℝ)+1) := moment
      _ = _ := by dsimp [n]; field_simp; ring
  have L (i : I) : -(1:ℝ)/13 ≤ e i/n := by
    apply (le_div_iff₀ np).mpr
    dsimp [n]
    linarith [lo i]
  calc
    _ ≤ ∏ i, (n*(1+e i/n)) := four_fifths_of_moments k hk card _ M V L
    _ = _ := Finset.prod_congr rfl fun i _ ↦ by change n*(1+e i/n) = n+e i; field_simp

/-- A deviation bounded in magnitude by `2*sqrt q` satisfies the one-sided
hypothesis at every `q≥674`, for Gram diagonal `q+1`. -/
theorem two_sqrt_le {q : ℝ} (hq : 674 ≤ q) : 2*Real.sqrt q ≤ (q+1)/13 := by
  rw [← sq_le_sq₀ (by positivity) (by linarith)]
  nlinarith [Real.sq_sqrt (show 0 ≤ q by linarith),
    mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ q-674 by linarith)]

/-- The real eigenvalues of the border block with entries `0,b,b,d` satisfy
the same lower bound as the character modes when `b²=2(q−1)` and `d≥−2`. -/
theorem border_eigenvalue_lower {q b d z : ℝ} (hq : 1 ≤ q) (hd : -2 ≤ d)
    (hb : b^2 = 2*(q-1)) (hz : z*(z-d) = b^2) : -2*Real.sqrt q ≤ z := by
  have sq := Real.sq_sqrt (show 0 ≤ q by linarith)
  have hs : 1 ≤ Real.sqrt q := (Real.one_le_sqrt).mpr hq
  by_contra! h
  have hf : 0 < (z+2*Real.sqrt q)*(z+2-2*Real.sqrt q) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hc : 0 ≤ (d+2)*(-z) := mul_nonneg (by linarith) (by linarith)
  nlinarith [sq_nonneg (Real.sqrt q-1)]

#print axioms four_fifths_gram_block
#print axioms two_sqrt_le
#print axioms border_eigenvalue_lower

end Hadamard.DeterminantRatio
