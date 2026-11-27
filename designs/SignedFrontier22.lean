import Signed22ColdPrime7

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem no_norm_cofactor_22 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*22) (hs : ¬ p∣22) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=22) hf hd hn hs (by decide)
  have all : ∀ t : Fin 44, Nat.Prime t.val → 3≤t.val → ¬t.val∣22 → t.val=3 ∨ t.val=5 ∨ t.val=7 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 ∨ t.val=37 ∨ t.val=41 ∨ t.val=43 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 3 22 3 2 1 0 11)
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 22 5 2 2 0 11)
  · change p=7 at hh; subst p
    exact fixed_7_22_false hf hg hm hn
  · change p=13 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 13 22 13 2 6 0 11)
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 22 17 2 4 0 11)
  · change p=19 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 19 22 19 2 9 0 11)
  · change p=23 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 23 22 23 11 11 0 2)
  · change p=29 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 29 22 29 2 14 0 11)
  · change p=31 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 31 22 31 11 15 0 2)
  · change p=37 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 37 22 37 11 3 0 2)
  · change p=41 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 41 22 41 2 10 0 11)
  · change p=43 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 43 22 43 2 7 0 11)

#print axioms no_norm_cofactor_22

end Signed39.Contraction
