import Signed19ColdPrime3
import Signed19ColdPrime31

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem no_norm_cofactor_19 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*19) (hs : ¬ p∣19) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=19) hf hd hn hs (by decide)
  have all : ∀ t : Fin 38, Nat.Prime t.val → 3≤t.val → ¬t.val∣19 → t.val=3 ∨ t.val=5 ∨ t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 ∨ t.val=37 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact fixed_3_19_false hf hg hm hn
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 19 5 19 1 0 1)
  · change p=7 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 7 19 7 19 3 0 1)
  · change p=11 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 11 19 11 19 5 0 1)
  · change p=13 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 13 19 13 19 6 0 1)
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 19 17 19 4 0 1)
  · change p=23 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 23 19 23 19 11 0 1)
  · change p=29 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 29 19 29 19 14 0 1)
  · change p=31 at hh; subst p
    exact fixed_31_19_false hf hg hm hn
  · change p=37 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 37 19 37 19 18 0 1)

#print axioms no_norm_cofactor_19

end Signed39.Contraction
