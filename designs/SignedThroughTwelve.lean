import SignedThroughTen
import SignedFrontier11
import SignedFrontier12

namespace Signed39.Contraction

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {p : ℕ} [Fact p.Prime]

theorem norm_cofactor_through_twelve {s : ℕ} {k l : ℤ} (hd : p∣Fintype.card G)
    (hn : k-l=(p:ℤ)*s) (hs : ¬p∣s) (lo : 1 ≤ s) (hi : s≤12) :
    (∃ f : G → ℤ, IsSDS k l f) ↔ s=1 ∧ Fintype.card G=p ∧ k=(p:ℤ)-1 ∧ l= -1 ∧ p≠2 := by
  by_cases h : s≤10
  · exact norm_cofactor_through_ten hd hn hs lo h
  constructor
  · rintro ⟨f,hf⟩
    rcases (show s=11 ∨ s=12 by omega) with rfl|rfl
    · exact False.elim (no_norm_cofactor_11 hf hd hn hs)
    · exact False.elim (no_norm_cofactor_12 hf hd hn hs)
  · rintro ⟨rfl,_⟩
    omega

#print axioms norm_cofactor_through_twelve

end Signed39.Contraction
