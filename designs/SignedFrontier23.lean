import SignedTwentyThreePrime7
import SignedTwentyThreePrime11
import SignedTwentyThreePrime19
import SignedTwentyThreePrime29
import SignedTwentyThreePrime43
namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_norm_cofactor_23 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*23) (hs : ¬ p∣23) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=23) hf hd hn hs (by decide)
  have all : ∀ t : Fin 46, Nat.Prime t.val → 3≤t.val → ¬t.val∣23 → t.val=3 ∨ t.val=5 ∨ t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=29 ∨ t.val=31 ∨ t.val=37 ∨ t.val=41 ∨ t.val=43 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 3 23 3 23 1 0 1)
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 23 5 23 2 0 1)
  · change p=7 at hh; subst p
    exact fixed_7_23_false hf hg hm hn
  · change p=11 at hh; subst p
    exact fixed_11_23_false hf hg hm hn
  · change p=13 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 13 23 13 23 3 0 1)
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 23 17 23 8 0 1)
  · change p=19 at hh; subst p
    exact fixed_19_23_false hf hg hm hn
  · change p=29 at hh; subst p
    exact fixed_29_23_false hf hg hm hn
  · change p=31 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 31 23 31 23 5 0 1)
  · change p=37 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 37 23 37 23 6 0 1)
  · change p=41 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 41 23 41 23 5 0 1)
  · change p=43 at hh; subst p
    exact fixed_43_23_false hf hg hm hn

#print axioms no_norm_cofactor_23

end Signed39.Contraction
