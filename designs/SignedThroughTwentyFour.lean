import SignedThroughTwentyTwo
import SignedFrontier23
import SignedFrontier24

namespace Signed39.Contraction

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {p : ℕ} [Fact p.Prime]

theorem norm_cofactor_through_twenty_four {s : ℕ} {k l : ℤ} (hd : p∣Fintype.card G)
    (hn : k-l=(p:ℤ)*s) (hs : ¬p∣s) (lo : 1 ≤ s) (hi : s ≤ 24) :
    (∃ f : G → ℤ, IsSDS k l f) ↔ s=1 ∧ Fintype.card G=p ∧ k=(p:ℤ)-1 ∧ l= -1 ∧ p≠2 := by
  by_cases h:s≤22
  · exact norm_cofactor_through_twenty_two hd hn hs lo h
  constructor
  · rintro ⟨f,hf⟩
    rcases (show s=23∨s=24 by omega) with rfl|rfl
    · exact False.elim (no_norm_cofactor_23 hf hd hn hs)
    · exact False.elim (no_norm_cofactor_24 hf hd hn hs)
  · rintro ⟨rfl,_⟩
    omega

#print axioms norm_cofactor_through_twenty_four

end Signed39.Contraction
