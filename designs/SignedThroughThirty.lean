import SignedThroughTwentyFour
import SignedFrontier25
import SignedFrontier26
import SignedFrontier27
import SignedFrontier28
import SignedFrontier29

namespace Signed39.Contraction

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {p : ℕ} [Fact p.Prime]

theorem norm_cofactor_through_thirty {s : ℕ} {k l : ℤ} (hd : p∣Fintype.card G)
    (hn : k-l=(p:ℤ)*s) (hs : ¬p∣s) (lo : 1 ≤ s) (hi : s ≤ 30) :
    (∃ f : G → ℤ, IsSDS k l f) ↔ s=1 ∧ Fintype.card G=p ∧ k=(p:ℤ)-1 ∧ l= -1 ∧ p≠2 := by
  by_cases small:s≤24
  · exact norm_cofactor_through_twenty_four hd hn hs lo small
  constructor
  · rintro ⟨f,hf⟩
    rcases (show s=25∨s=26∨s=27∨s=28∨s=29∨s=30 by omega) with rfl|rfl|rfl|rfl|rfl|rfl
    · exact False.elim (no_norm_cofactor_25 hf hd hn hs)
    · exact False.elim (no_norm_cofactor_26 hf hd hn hs)
    · exact False.elim (no_norm_cofactor_27 hf hd hn hs)
    · exact False.elim (no_norm_cofactor_28 hf hd hn hs)
    · exact False.elim (no_norm_cofactor_29 hf hd hn hs)
    · exact False.elim (no_sieved_norm_cofactor hf hd hn hs (by decide))
  · rintro ⟨rfl,_⟩
    omega

#print axioms norm_cofactor_through_thirty

end Signed39.Contraction

