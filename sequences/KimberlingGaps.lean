import KimberlingCore

namespace KimberlingMoses

/-- Consecutive elements of the good-index set with difference `g`. -/
def OccursGap (b : ℕ → ℕ) (g : ℕ) : Prop :=
  0 < g ∧ ∃ i, Good b i ∧ Good b (i+g) ∧ ∀ j, 0 < j → j < g → ¬Good b (i+j)

theorem bit_nine_one (q : ℕ) : bit (9*q+1) = true := by
  rw [show 9*q+1 = 3*(3*q)+1 by omega, bit_one, bit_zero]; rfl

theorem bit_nine_five (q : ℕ) : bit (9*q+5) = true := by
  rw [show 9*q+5 = 3*(3*q+1)+2 by omega, bit_two,
    show 2*(3*q+1)+1 = 3*(2*q+1) by omega, bit_zero]; rfl

theorem good_within_five {a b : ℕ → ℕ} (h : Solution a b) (n : ℕ) :
    ∃ i, n ≤ i ∧ i ≤ n+4 ∧ Good b i := by
  let q := n/9
  have cases : (n ≤ 9*q+1 ∧ 9*q+1 ≤ n+4) ∨ (n ≤ 9*q+5 ∧ 9*q+5 ≤ n+4) ∨
      (n ≤ 9*(q+1)+1 ∧ 9*(q+1)+1 ≤ n+4) := by dsimp [q]; omega
  rcases cases with h1|h5|hn
  · exact ⟨_, h1.1, h1.2, (good_iff_bit h _).mpr (bit_nine_one _)⟩
  · exact ⟨_, h5.1, h5.2, (good_iff_bit h _).mpr (bit_nine_five _)⟩
  · exact ⟨_, hn.1, hn.2, (good_iff_bit h _).mpr (bit_nine_one _)⟩

private def evalBit : ℕ → ℕ → Bool
  | 0, _ => false
  | depth+1, n =>
    if n%3 = 0 then false else if n%3 = 1 then !(evalBit depth (n/3))
    else !(evalBit depth (2*(n/3)+1))

private theorem evalBit_eq (depth n : ℕ) (hn : n ≤ depth) : evalBit depth n = bit n := by
  induction depth generalizing n with
  | zero => have : n = 0 := by omega
            subst n; rw [bit]; rfl
  | succ d ih =>
    rw [evalBit, bit]
    split_ifs with h0 h1
    · rfl
    · rw [ih (n/3) (by omega)]
    · rw [ih (2*(n/3)+1) (by omega)]

private theorem witness_gap {a b : ℕ → ℕ} (h : Solution a b) (i g : ℕ)
    (hg : 0 < g) (left : evalBit (i+g) i = true) (right : evalBit (i+g) (i+g) = true)
    (middle : ∀ j : Fin g, 0 < j.val → evalBit (i+g) (i+j.val) = false) : OccursGap b g := by
  rw [evalBit_eq _ _ (by omega)] at left right
  refine ⟨hg, i, (good_iff_bit h _).mpr left, (good_iff_bit h _).mpr right, ?_⟩
  intro j hj hjg hgood
  have he := middle ⟨j,hjg⟩ hj
  rw [evalBit_eq _ _ (by omega), (good_iff_bit h _).mp hgood] at he; contradiction

/-- Kimberling–Moses Conjecture 18 (JIS 24, Article 21.3.3). -/
theorem conjecture18 {a b : ℕ → ℕ} (h : Solution a b) (g : ℕ) :
    OccursGap b g ↔ 1 ≤ g ∧ g ≤ 5 := by
  constructor
  · rintro ⟨hg,i,_,_,hn⟩
    refine ⟨hg, ?_⟩; by_contra! hmore
    obtain ⟨j,hlo,hhi,hgood⟩ := good_within_five h (i+1)
    have hnone := hn (j-i) (by omega) (by omega)
    rw [show i+(j-i)=j by omega] at hnone; exact hnone hgood
  · rintro ⟨hg1,hg5⟩; interval_cases g
    · exact witness_gap h 13 1 (by decide) (by decide) (by decide) (by decide)
    · exact witness_gap h 5 2 (by decide) (by decide) (by decide) (by decide)
    · exact witness_gap h 7 3 (by decide) (by decide) (by decide) (by decide)
    · exact witness_gap h 1 4 (by decide) (by decide) (by decide) (by decide)
    · exact witness_gap h 68 5 (by decide) (by decide) (by decide) (by decide)

#print axioms conjecture18

end KimberlingMoses
