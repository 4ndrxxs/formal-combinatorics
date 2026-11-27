import KimberlingCore

open Finset Filter Topology

namespace KimberlingMoses

/-- Five times the indicator of a good index, centered at its conjectured mean. -/
def centered (n : ℕ) : ℝ := if bit n then 3 else -2

@[simp] theorem centered_zero (q : ℕ) : centered (3*q) = -2 := by simp [centered]

theorem centered_one (q : ℕ) : centered (3*q+1) = 1 - centered q := by
  unfold centered; rw [bit_one]; cases bit q <;> norm_num

theorem centered_two (q : ℕ) : centered (3*q+2) = 1 - centered (2*q+1) := by
  unfold centered; rw [bit_two]; cases bit (2*q+1) <;> norm_num

theorem centered_abs (n : ℕ) : |centered n| ≤ 3 := by
  unfold centered; split_ifs <;> norm_num

/-- Sum of centered values on the first `N` terms of an arithmetic progression. -/
def progressionSum (a b N : ℕ) : ℝ := ∑ i ∈ range N, centered (a*i+b)

theorem group_triples (f : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range (3*N), f i = (∑ i ∈ range N, f (3*i)) +
      (∑ i ∈ range N, f (3*i+1)) + ∑ i ∈ range N, f (3*i+2) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 3*(n+1) = 3*n+1+1+1 by omega]
    simp only [sum_range_succ]
    rw [ih]; ring

private theorem three_part_term (a b s i : ℕ) :
    centered (a*(3*i+s)+b) = if (a*s+b)%3 = 0 then -2 else
      if (a*s+b)%3 = 1 then 1 - centered (a*i+(a*s+b)/3)
      else 1 - centered ((2*a)*i+(2*((a*s+b)/3)+1)) := by
  have h : a*(3*i+s)+b = 3*(a*i+(a*s+b)/3)+(a*s+b)%3 := by
    have t := Nat.div_add_mod (a*s+b) 3
    calc
      a*(3*i+s)+b = 3*(a*i)+(a*s+b) := by ring
      _ = _ := by omega
  rw [h]
  split_ifs with h0 h1
  · rw [h0, Nat.add_zero, centered_zero]
  · rw [h1, centered_one]
  · have h2 : (a*s+b)%3 = 2 := by omega
    rw [h2, centered_two]; congr 2; ring

private def segment (a b s N : ℕ) : ℝ :=
  if (a*s+b)%3 = 0 then -2*N else
  if (a*s+b)%3 = 1 then N - progressionSum a ((a*s+b)/3) N
  else N - progressionSum (2*a) (2*((a*s+b)/3)+1) N

private theorem segment_eq (a b s N : ℕ) :
    ∑ i ∈ range N, centered (a*(3*i+s)+b) = segment a b s N := by
  simp_rw [three_part_term]; unfold segment
  split_ifs <;> simp [progressionSum, sum_sub_distrib]; ring

theorem three_residues (a b : ℕ) (ha : a%3 ≠ 0) :
    (b%3=0 ∧ (a+b)%3=1 ∧ (2*a+b)%3=2) ∨
    (b%3=0 ∧ (a+b)%3=2 ∧ (2*a+b)%3=1) ∨
    (b%3=1 ∧ (a+b)%3=0 ∧ (2*a+b)%3=2) ∨
    (b%3=1 ∧ (a+b)%3=2 ∧ (2*a+b)%3=0) ∨
    (b%3=2 ∧ (a+b)%3=0 ∧ (2*a+b)%3=1) ∨
    (b%3=2 ∧ (a+b)%3=1 ∧ (2*a+b)%3=0) := by
  have am : a%3=1 ∨ a%3=2 := by omega
  have bm : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
  rcases am with h | h <;> rcases bm with k | k | k <;>
    simp [Nat.add_mod, Nat.mul_mod, h,k]

/-- Exactly two progressions survive each ternary step. -/
theorem trisect (a b N : ℕ) (ha : a%3 ≠ 0) : ∃ c d,
    progressionSum a b (3*N) = -progressionSum a c N - progressionSum (2*a) d N := by
  have hs : progressionSum a b (3*N) = segment a b 0 N + segment a b 1 N + segment a b 2 N := by
    unfold progressionSum; rw [group_triples]
    simpa only [Nat.add_zero] using congrArg₂ (· + ·)
      (congrArg₂ (· + ·) (segment_eq a b 0 N) (segment_eq a b 1 N)) (segment_eq a b 2 N)
  have hseg := three_residues a b ha
  rw [hs]; unfold segment; simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.mul_comm a 2]
  rcases hseg with ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩
  · exact ⟨(a+b)/3, 2*((2*a+b)/3)+1, by simp [h0,h1,h2]; ring⟩
  · exact ⟨(2*a+b)/3, 2*((a+b)/3)+1, by simp [h0,h1,h2]; ring⟩
  · exact ⟨b/3, 2*((2*a+b)/3)+1, by simp [h0,h1,h2]; ring⟩
  · exact ⟨b/3, 2*((a+b)/3)+1, by simp [h0,h1,h2]; ring⟩
  · exact ⟨(2*a+b)/3, 2*(b/3)+1, by simp [h0,h1,h2]; ring⟩
  · exact ⟨(a+b)/3, 2*(b/3)+1, by simp [h0,h1,h2]; ring⟩

/-- Uniform discrepancy bound on every admissible progression of length `3^h`. -/
theorem block_discrepancy (h a b : ℕ) (ha : a%3 ≠ 0) :
    |progressionSum a b (3^h)| ≤ 3 * (2:ℝ)^h := by
  induction h generalizing a b with
  | zero => simpa [progressionSum] using centered_abs b
  | succ h ih =>
    rw [pow_succ', pow_succ']
    obtain ⟨c,d,he⟩ := trisect a b (3^h) ha
    rw [he, sub_eq_add_neg]
    calc
      _ ≤ |-progressionSum a c (3^h)| + |-progressionSum (2*a) d (3^h)| := abs_add_le ..
      _ ≤ _ := by rw [abs_neg,abs_neg]; linarith [ih a c ha, ih (2*a) d (by omega)]

theorem sum_append (a b m n : ℕ) :
    progressionSum a b (m+n) = progressionSum a b m + progressionSum a (a*m+b) n := by
  simp only [progressionSum, sum_range_add]; congr 1
  apply sum_congr rfl; intro i _; congr 1; ring

private theorem many_blocks (h b q : ℕ) :
    |progressionSum 1 b (3^h*q)| ≤ (q:ℝ)*(3*2^h) := by
  induction q with
  | zero => simp [progressionSum]
  | succ q ih =>
    rw [Nat.mul_succ, sum_append]
    calc
      _ ≤ |progressionSum 1 b (3^h*q)| + |progressionSum 1 (1*(3^h*q)+b) (3^h)| := abs_add_le ..
      _ ≤ _ := by push_cast; linarith [block_discrepancy h 1 (1*(3^h*q)+b) (by decide)]

private theorem trivial_discrepancy (a b N : ℕ) : |progressionSum a b N| ≤ 3*N := by
  calc
    _ ≤ ∑ i ∈ range N, |centered (a*i+b)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range N, (3:ℝ) := sum_le_sum fun i _ => centered_abs _
    _ = _ := by simp; ring

/-- Prefix estimate, including the final incomplete block. -/
theorem prefix_discrepancy (h N : ℕ) :
    |progressionSum 1 0 N| ≤ N * (3*(2/3:ℝ)^h) + 3*(3:ℝ)^h := by
  let L : ℕ := 3^h
  have hL : 0 < L := by dsimp [L]; positivity
  have hmod : N%L ≤ L := (Nat.mod_lt _ hL).le
  have hq : ((N/L:ℕ):ℝ)*L ≤ N := by exact_mod_cast Nat.div_mul_le_self N L
  have hL' : (L:ℝ) = (3:ℝ)^h := by simp [L]
  have hfactor : 3*(2:ℝ)^h = (L:ℝ)*(3*(2/3:ℝ)^h) := by rw [hL',div_pow]; field_simp
  have hfirst : ((N/L:ℕ):ℝ)*(3*2^h) ≤ N*(3*(2/3:ℝ)^h) := by
    rw [hfactor, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hq (by positivity)
  have hlast : 3*((N%L:ℕ):ℝ) ≤ 3*(3:ℝ)^h := by rw [← hL']; exact_mod_cast Nat.mul_le_mul_left 3 hmod
  calc
    _ = |progressionSum 1 0 (L*(N/L)+N%L)| := by rw [Nat.div_add_mod]
    _ ≤ |progressionSum 1 0 (L*(N/L))| + |progressionSum 1 (1*(L*(N/L))+0) (N%L)| := by
      rw [sum_append]; exact abs_add_le ..
    _ ≤ _ := add_le_add ((many_blocks h 0 (N/L)).trans hfirst)
      ((trivial_discrepancy _ _ (N%L)).trans hlast)

/-- Relative frequency of good positions in the zero-based prefix `[0,N)`. -/
noncomputable def proportion (b : ℕ → ℕ) (N : ℕ) : ℝ := ((range N).filter (Good b)).card / (N:ℝ)

theorem centered_count {a b : ℕ → ℕ} (sol : Solution a b) (N : ℕ) :
    progressionSum 1 0 N = 5 * (((range N).filter (Good b)).card:ℝ) - 2*N := by
  have eqn (i : ℕ) : centered i = 5*(if Good b i then (1:ℝ) else 0)-2 := by
    simp only [good_iff_bit sol]; unfold centered; cases bit i <;> norm_num
  simp only [progressionSum, Nat.one_mul, Nat.add_zero, eqn, sum_sub_distrib, ← Finset.mul_sum, sum_boole]
  simp; ring

/-- Kimberling–Moses Conjecture 19 (JIS 24, Article 21.3.3). -/
theorem conjecture19 {a b : ℕ → ℕ} (sol : Solution a b) :
    Tendsto (proportion b) atTop (𝓝 (2/5:ℝ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num : (2/3:ℝ) < 1)
  obtain ⟨h,hh⟩ := (hp.eventually_lt_const hε).exists
  have ht : Tendsto (fun n : ℕ => (3*(3:ℝ)^h)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop _
  obtain ⟨N0,hN0⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const hε)
  refine ⟨max 1 N0, ?_⟩; intro N hN
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr := hN0 N (by omega)
  have hb := prefix_discrepancy h N
  rw [centered_count sol] at hb
  rw [Real.dist_eq, proportion]
  have hd : (((range N).filter (Good b)).card:ℝ)/(N:ℝ) - 2/5 =
      (5*(((range N).filter (Good b)).card:ℝ) - 2*N)/(5*N) := by field_simp
  rw [hd,abs_div,abs_of_pos (by positivity : (0:ℝ)<5*N),div_lt_iff₀ (by positivity)]
  have hc := (div_lt_iff₀ hn).mp hr
  have hs := mul_lt_mul_of_pos_left hh hn
  nlinarith only [hb,hc,hs,mul_pos hn hε]

#print axioms conjecture19

end KimberlingMoses
