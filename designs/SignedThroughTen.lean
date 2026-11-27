import SignedExtendedClassification
import SignedNinePrime5
import SignedNinePrime7
import SignedNinePrime11
import SignedNinePrime13
import SignedNinePrime17

/-! The signed difference set parameters whose simple common prime has norm cofactor at most ten. -/

namespace Signed39.Contraction

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {p : ℕ} [Fact p.Prime]

theorem no_norm_cofactor_nine {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hd : p∣Fintype.card G) (hn : k-lam=(p:ℤ)*9) (hs : ¬p∣9) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=9) hf hd hn hs (by decide)
  have list : ∀ a : Fin 18, 3≤a.val → Nat.Prime a.val → ¬a.val∣9 →
      a.val=5 ∨ a.val=7 ∨ a.val=11 ∨ a.val=13 ∨ a.val=17 := by decide +kernel
  rcases list ⟨p,by omega⟩ p3 Fact.out hs with h|h|h|h|h
  · change p=5 at h; subst p; exact fixed_nine_5 hf hg hm hn
  · change p=7 at h; subst p; exact fixed_nine_7 hf hg hm hn
  · change p=11 at h; subst p; exact fixed_nine_11 hf hg hm hn
  · change p=13 at h; subst p; exact fixed_nine_13 hf hg hm hn
  · change p=17 at h; subst p; exact fixed_nine_17 hf hg hm hn

/-- For 1≤s≤10 with p dividing the group order exactly to first order in the norm ps,
the only possible parameter set is the odd-prime Paley parameter set, which is attained. -/
theorem norm_cofactor_through_ten {s : ℕ} {k lam : ℤ} (hd : p∣Fintype.card G)
    (hn : k-lam=(p:ℤ)*s) (hs : ¬p∣s) (lo : 1 ≤ s) (hi : s≤10) :
    (∃ f : G → ℤ, IsSDS k lam f) ↔ s=1 ∧ Fintype.card G=p ∧ k=(p:ℤ)-1 ∧ lam= -1 ∧ p≠2 := by
  by_cases small : s≤8
  · exact norm_cofactor_through_eight hd hn hs lo small
  constructor
  · rintro ⟨f,hf⟩
    rcases (show s=9 ∨ s=10 by omega) with rfl|rfl
    · exact False.elim (no_norm_cofactor_nine hf hd hn hs)
    · exact False.elim (no_sieved_norm_cofactor hf hd hn hs (by unfold sieveCofactor; omega))
  · rintro ⟨rfl,_⟩
    omega

#print axioms no_norm_cofactor_nine
#print axioms norm_cofactor_through_ten

end Signed39.Contraction
