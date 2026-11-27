import PermanentFourExclusion
import PermanentFourEuler
import PermanentFourTernary11
import PermanentFourTernary15
import PermanentOrderFourWitness04
import PermanentOrderFourWitness06
import PermanentOrderFourWitness08
import PermanentOrderFourWitness09
import PermanentOrderFourWitness10
import PermanentOrderFourWitness11
import PermanentOrderFourWitness12
import PermanentOrderFourWitness13
import PermanentOrderFourWitness14
import PermanentOrderFourWitness15
import PermanentOrderFourWitness16
/-! The complete spectrum of Hessian ranks at smooth zeros of the
order-four permanent over every field of characteristic different from two. -/
noncomputable section
open Matrix PermanentFive QuinticPencil PermanentBorder PermanentOrderThree
namespace PermanentOrderFour
variable {K : Type*} [Field K]
theorem fixed_four_odd (two_ne : (2:K)≠0) (s : ℕ) :
    AtOrder K 4 s ↔ s=4 ∨ s=6 ∨ (8≤s ∧ s≤16 ∧ (s=16 → (3:K)≠0)) := by
  constructor
  · rintro ⟨z,flat,smooth,hs⟩
    have gap := permanent_hessian_rank_gap z
    have pos := smooth_positive z smooth
    have seven := seven_excluded two_ne z flat smooth
    have top := Matrix.rank_le_card_width (hessian (per K F) z)
    change (hessian (per K F) z).rank≤16 at top
    unfold F at top seven
    have last : s=16 → (3:K)≠0 := by
      intro large bad
      have cap := characteristic_three_cap bad z smooth
      unfold F at cap
      omega
    have possible : s=4 ∨ s=6 ∨ (8≤s ∧ s≤16) := by omega
    rcases possible with v|v|⟨lo,hi⟩
    · exact Or.inl v
    · exact Or.inr (Or.inl v)
    · exact Or.inr (Or.inr ⟨lo,hi,last⟩)
  · intro allowed
    have vals : s=4 ∨ s=6 ∨ s=8 ∨ s=9 ∨ s=10 ∨ s=11 ∨ s=12 ∨ s=13 ∨ s=14 ∨ s=15 ∨ s=16 := by omega
    rcases vals with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact over_field_4 K two_ne
    · exact over_field_6 K two_ne
    · exact over_field_8 K
    · exact over_field_9 K two_ne
    · exact over_field_10 K two_ne
    · by_cases three_zero : (3:K)=0
      · exact characteristic_three_11 K three_zero
      · exact over_field_11 K two_ne three_zero
    · exact over_field_12 K two_ne
    · exact over_field_13 K two_ne
    · exact over_field_14 K two_ne
    · by_cases three_zero : (3:K)=0
      · exact characteristic_three_15 K three_zero
      · exact over_field_15 K two_ne three_zero
    · have three_ne : (3:K)≠0 := by rcases allowed with h|h|h <;> first | omega | exact h.2.2 rfl
      exact over_field_16 K two_ne three_ne

theorem fixed_four_spectrum [CharZero K] (s : ℕ) :
    AtOrder K 4 s ↔ s=4 ∨ s=6 ∨ (8≤s ∧ s≤16) := by
  rw [fixed_four_odd (by norm_num : (2:K)≠0)]; simp

theorem fixed_four_characteristic_three (three_zero : (3:K)=0) (s : ℕ) :
    AtOrder K 4 s ↔ s=4 ∨ s=6 ∨ (8≤s ∧ s≤15) := by
  have two_ne : (2:K)≠0 := by
    intro h
    apply one_ne_zero (α:=K)
    linear_combination three_zero-h
  rw [fixed_four_odd two_ne]
  simp only [three_zero,ne_eq,not_true_eq_false,imp_false]
  omega

#print axioms fixed_four_odd
#print axioms fixed_four_spectrum
#print axioms fixed_four_characteristic_three
end PermanentOrderFour
