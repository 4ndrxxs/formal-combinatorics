import SignedThroughTwelve
import SignedFrontier13
import SignedFrontier15

namespace Signed39.Contraction

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {p : ℕ} [Fact p.Prime]

theorem norm_cofactor_through_fifteen {s : ℕ} {k l : ℤ} (hd : p∣Fintype.card G)
    (hn : k-l=(p:ℤ)*s) (hs : ¬p∣s) (lo : 1 ≤ s) (hi : s≤15) :
    (∃ f : G → ℤ, IsSDS k l f) ↔ s=1 ∧ Fintype.card G=p ∧ k=(p:ℤ)-1 ∧ l= -1 ∧ p≠2 := by
  by_cases h : s≤12
  · exact norm_cofactor_through_twelve hd hn hs lo h
  constructor
  · rintro ⟨f,hf⟩
    rcases (show s=13 ∨ s=14 ∨ s=15 by omega) with rfl|rfl|rfl
    · exact False.elim (no_norm_cofactor_13 hf hd hn hs)
    · exact False.elim (no_sieved_norm_cofactor hf hd hn hs (by decide : sieveCofactor 14))
    · exact False.elim (no_norm_cofactor_15 hf hd hn hs)
  · rintro ⟨rfl,_⟩
    omega

#print axioms norm_cofactor_through_fifteen

end Signed39.Contraction
