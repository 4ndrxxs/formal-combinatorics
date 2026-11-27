import Signed24ColdPrime23
import Signed24ColdPrime47

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem no_norm_cofactor_24 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*24) (hs : ¬ p∣24) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=24) hf hd hn hs (by decide)
  have all : ∀ t : Fin 48, Nat.Prime t.val → 3≤t.val → ¬t.val∣24 → t.val=5 ∨ t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 ∨ t.val=37 ∨ t.val=41 ∨ t.val=43 ∨ t.val=47 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 24 5 3 2 0 8)
  · change p=7 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 7 24 7 3 3 0 8)
  · change p=11 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 11 24 11 2 5 1 3)
  · change p=13 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 13 24 13 2 6 1 3)
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 24 17 2 4 1 3)
  · change p=19 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 19 24 19 3 9 0 8)
  · change p=23 at hh; subst p
    exact fixed_23_24_false hf hg hm hn
  · change p=29 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 29 24 29 3 14 0 8)
  · change p=31 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 31 24 31 3 15 0 8)
  · change p=37 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 37 24 37 3 9 0 8)
  · change p=41 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 41 24 41 3 4 0 8)
  · change p=43 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 43 24 43 2 7 1 3)
  · change p=47 at hh; subst p
    exact fixed_47_24_false hf hg hm hn

#print axioms no_norm_cofactor_24

end Signed39.Contraction
