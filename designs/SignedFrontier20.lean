import Signed20ColdPrime11
import Signed20ColdPrime19
import Signed20ColdPrime31

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem no_norm_cofactor_20 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*20) (hs : ¬ p∣20) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=20) hf hd hn hs (by decide)
  have all : ∀ t : Fin 40, Nat.Prime t.val → 3≤t.val → ¬t.val∣20 → t.val=3 ∨ t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 ∨ t.val=37 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 3 20 3 5 1 0 4)
  · change p=7 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 7 20 7 5 3 0 4)
  · change p=11 at hh; subst p
    exact fixed_11_20_false hf hg hm hn
  · change p=13 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 13 20 13 5 2 0 4)
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 20 17 5 8 0 4)
  · change p=19 at hh; subst p
    exact fixed_19_20_false hf hg hm hn
  · change p=23 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 23 20 23 5 11 0 4)
  · change p=29 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 29 20 29 5 7 0 4)
  · change p=31 at hh; subst p
    exact fixed_31_20_false hf hg hm hn
  · change p=37 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 37 20 37 5 18 0 4)

#print axioms no_norm_cofactor_20

end Signed39.Contraction
