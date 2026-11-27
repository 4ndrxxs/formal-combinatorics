import SignedSixteenPrime3
import SignedSixteenPrime5
import SignedSixteenPrime7
import SignedSixteenPrime11
import SignedSixteenPrime13
import SignedSixteenPrime17
import SignedSixteenPrime19
import SignedSixteenPrime23
import SignedSixteenPrime29
import SignedSixteenPrime31
namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_norm_cofactor_16 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*16) (hs : ¬ p∣16) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=16) hf hd hn hs (by decide)
  have all : ∀ t : Fin 32, Nat.Prime t.val → 3≤t.val → ¬t.val∣16 → t.val=3 ∨ t.val=5 ∨ t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact fixed_3_16_false hf hg hm hn
  · change p=5 at hh; subst p
    exact fixed_5_16_false hf hg hm hn
  · change p=7 at hh; subst p
    exact fixed_7_16_false hf hg hm hn
  · change p=11 at hh; subst p
    exact fixed_11_16_false hf hg hm hn
  · change p=13 at hh; subst p
    exact fixed_13_16_false hf hg hm hn
  · change p=17 at hh; subst p
    exact fixed_17_16_false hf hg hm hn
  · change p=19 at hh; subst p
    exact fixed_19_16_false hf hg hm hn
  · change p=23 at hh; subst p
    exact fixed_23_16_false hf hg hm hn
  · change p=29 at hh; subst p
    exact fixed_29_16_false hf hg hm hn
  · change p=31 at hh; subst p
    exact fixed_31_16_false hf hg hm hn

#print axioms no_norm_cofactor_16

end Signed39.Contraction
