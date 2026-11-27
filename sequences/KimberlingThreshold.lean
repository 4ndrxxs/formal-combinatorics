import KimberlingBlocks

namespace KimberlingMoses

/-- Equation (17) in the paper. The constant is signed, as in Conjecture 20. -/
structure AdvancedSolution (u v k : ℕ) (c : ℤ) (a b : ℕ → ℕ) : Prop extends Complementary a b where
  initial : b 0 = 1
  equation : ∀ n, (a n:ℤ) = u*(b n:ℤ) + v*(b (n+k):ℤ) + c

abbrev negativeA := blockA 2 (fun _ => 2)
abbrev negativeB := blockB 2 (fun _ => 2)

private theorem negativeB_zero (q : ℕ) : negativeB (2*q) = 3*q+1 := by
  simpa [negativeB,skip] using blockB_at 2 (by decide) (fun _ => 2) q 0 (by decide)

private theorem negativeB_one (q : ℕ) : negativeB (2*q+1) = 3*q+3 := by
  simpa [negativeB,skip] using blockB_at 2 (by decide) (fun _ => 2) q 1 (by decide)

theorem negative_solution : AdvancedSolution 1 1 1 (-2) negativeA negativeB where
  toComplementary := block_complementary 2 (by decide) _ (by intro q; decide)
  initial := by decide
  equation n := by
    obtain ⟨q,h|h⟩ : ∃q, n=2*q ∨ n=2*q+1 := ⟨n/2,by omega⟩
    · subst n; rw [negativeB_zero,negativeB_one]; unfold negativeA blockA; push_cast; ring
    · subst n; rw [negativeB_one,show 2*q+1+1=2*(q+1) by omega,negativeB_zero]
      unfold negativeA blockA; push_cast; ring

private theorem negative_eq {a b : ℕ → ℕ} (h : AdvancedSolution 1 1 1 (-2) a b) (n : ℕ) :
    a n + 2 = b n + b (n+1) := by
  have he := h.equation n; norm_num at he; omega

private theorem negative_initial {a b : ℕ → ℕ} (h : AdvancedSolution 1 1 1 (-2) a b) :
    a 0=2 ∧ b 1=3 := by
  have he := negative_eq h 0; rw [h.initial] at he; norm_num at he
  have non := h.disjoint 0 0; rw [h.initial] at non
  have pos := h.positiveA 0
  have up : b 1 ≤ 3 := by
    by_contra! big
    rcases h.covers 2 (by decide) with ⟨i,hi⟩ | ⟨j,hj⟩
    · have ht := h.strictA.monotone (Nat.zero_le i); omega
    · by_cases hz : j=0
      · subst j; rw [h.initial] at hj; omega
      · have ht := h.strictB.monotone (show 1≤j by omega); omega
  omega

private theorem negative_no_first_less {a b a' b' : ℕ → ℕ}
    (h : AdvancedSolution 1 1 1 (-2) a b) (h' : AdvancedSolution 1 1 1 (-2) a' b')
    (j : ℕ) (agree : ∀ i<j, b i=b' i) : ¬b j < b' j := by
  intro less
  obtain ⟨_,hb⟩ := negative_initial h
  obtain ⟨ha',hb'⟩ := negative_initial h'
  have hj : 1<j := by
    by_contra! H; interval_cases j
    · rw [h.initial,h'.initial] at less; omega
    · omega
  have gt := h.strictB hj
  rcases h'.covers (b j) (h.positiveB j) with ⟨m,hm⟩ | ⟨i,hi⟩
  · have hm0 : 0 < m := by
      by_contra! hm0
      have eq : m = 0 := by omega
      rw [eq,ha'] at hm; omega
    have hb1 := h'.strictB.monotone (show 1 ≤ m by omega)
    have hb2 := h'.strictB.monotone (show 1 ≤ m+1 by omega)
    have he := negative_eq h' m
    have h1 : m<j := h'.strictB.lt_iff_lt.mp (by omega)
    have h2 : m+1<j := h'.strictB.lt_iff_lt.mp (by omega)
    have other := negative_eq h m
    rw [agree m h1,agree (m+1) h2] at other; exact h.disjoint m j (by omega)
  · have hij : i<j := h'.strictB.lt_iff_lt.mp (by omega)
    have ht := h.strictB hij; rw [agree i hij] at ht; omega

theorem negative_unique {a b a' b' : ℕ → ℕ}
    (h : AdvancedSolution 1 1 1 (-2) a b) (h' : AdvancedSolution 1 1 1 (-2) a' b') : a=a' ∧ b=b' := by
  have hb : ∀ j, b j=b' j := by
    intro j; induction j using Nat.strong_induction_on with
    | ind j ih =>
      have h1 := negative_no_first_less h h' j ih
      have h2 := negative_no_first_less h' h j (fun i hij => (ih i hij).symm)
      omega
  refine ⟨funext fun j => ?_, funext hb⟩
  have he := negative_eq h j; have he' := negative_eq h' j
  rw [hb,hb] at he; omega

theorem conjecture20_unique_below_threshold :
    ∃! ab : (ℕ → ℕ) × (ℕ → ℕ), AdvancedSolution 1 1 1 (-2) ab.1 ab.2 := by
  refine ⟨⟨negativeA,negativeB⟩,negative_solution,?_⟩
  rintro ⟨a,b⟩ h
  obtain ⟨ha,hb⟩ := negative_unique h negative_solution
  exact Prod.ext ha hb

/-- The exact quantified uniqueness criterion in Conjecture 20 is false. -/
theorem conjecture20_false : ¬∀ (u v k : ℕ) (c : ℤ), 1≤k → 1≤u → u≤v →
    ((∃! ab : (ℕ → ℕ) × (ℕ → ℕ), AdvancedSolution u v k c ab.1 ab.2) ↔
      2-(u:ℤ)-v+k-(v:ℤ)*k ≤ c) := by
  intro claim
  have bad := (claim 1 1 1 (-2) (by decide) (by decide) (by decide)).mp conjecture20_unique_below_threshold
  norm_num at bad

#print axioms conjecture20_unique_below_threshold
#print axioms conjecture20_false

end KimberlingMoses
