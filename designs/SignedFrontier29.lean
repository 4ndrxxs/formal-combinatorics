import Signed29Prime7
import Signed29Prime13
import Signed29Prime23

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_norm_cofactor_29 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*29) (hs : ¬ p∣29) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=29) hf hd hn hs (by decide)
  have all : ∀ t : Fin 58, Nat.Prime t.val → 3≤t.val → ¬t.val∣29 → t.val=3 ∨ t.val=5 ∨ t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=31 ∨ t.val=37 ∨ t.val=41 ∨ t.val=43 ∨ t.val=47 ∨ t.val=53 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 3 29 3 29 1 0 1)
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 29 5 29 1 0 1)
  · change p=7 at hh; subst p
    exact fixed_7_29_false hf hg hm hn
  · change p=11 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 11 29 11 29 5 0 1)
  · change p=13 at hh; subst p
    exact fixed_13_29_false hf hg hm hn
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 29 17 29 8 0 1)
  · change p=19 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 19 29 19 29 9 0 1)
  · change p=23 at hh; subst p
    exact fixed_23_29_false hf hg hm hn
  · change p=31 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 31 29 31 29 5 0 1)
  · change p=37 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 37 29 37 29 6 0 1)
  · change p=41 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 41 29 41 29 20 0 1)
  · change p=43 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 43 29 43 29 21 0 1)
  · change p=47 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 47 29 47 29 23 0 1)
  · change p=53 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 53 29 53 29 13 0 1)

#print axioms no_norm_cofactor_29

end Signed39.Contraction
