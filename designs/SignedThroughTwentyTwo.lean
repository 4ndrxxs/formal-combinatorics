import SignedThroughFifteen
import SignedFrontier16
import SignedFrontier17
import SignedFrontier18
import SignedFrontier19
import SignedFrontier20
import SignedFrontier22

namespace Signed39.Contraction

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {p : ℕ} [Fact p.Prime]

theorem norm_cofactor_through_twenty_two {s : ℕ} {k l : ℤ} (hd : p∣Fintype.card G)
    (hn : k-l=(p:ℤ)*s) (hs : ¬p∣s) (lo : 1 ≤ s) (hi : s ≤ 22) :
    (∃ f : G → ℤ, IsSDS k l f) ↔ s=1 ∧ Fintype.card G=p ∧ k=(p:ℤ)-1 ∧ l= -1 ∧ p≠2 := by
  by_cases h:s≤15
  · exact norm_cofactor_through_fifteen hd hn hs lo h
  constructor
  · rintro ⟨f,hf⟩
    rcases (show s=16∨s=17∨s=18∨s=19∨s=20∨s=21∨s=22 by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact False.elim (no_norm_cofactor_16 hf hd hn hs)
    · exact False.elim (no_norm_cofactor_17 hf hd hn hs)
    · exact False.elim (no_norm_cofactor_18 hf hd hn hs)
    · exact False.elim (no_norm_cofactor_19 hf hd hn hs)
    · exact False.elim (no_norm_cofactor_20 hf hd hn hs)
    · exact False.elim (no_sieved_norm_cofactor hf hd hn hs (by decide : sieveCofactor 21))
    · exact False.elim (no_norm_cofactor_22 hf hd hn hs)
  · rintro ⟨rfl,_⟩
    omega

#print axioms norm_cofactor_through_twenty_two

end Signed39.Contraction
