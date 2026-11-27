import Signed18ColdPrime7
import Signed18ColdPrime23
import Signed18ColdPrime31

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem no_norm_cofactor_18 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*18) (hs : ¬ p∣18) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=18) hf hd hn hs (by decide)
  have all : ∀ t : Fin 36, Nat.Prime t.val → 3≤t.val → ¬t.val∣18 → t.val=5 ∨ t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 18 5 2 2 0 9)
  · change p=7 at hh; subst p
    exact fixed_7_18_false hf hg hm hn
  · change p=11 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 11 18 11 2 5 0 9)
  · change p=13 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 13 18 13 2 6 0 9)
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 18 17 2 4 0 9)
  · change p=19 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 19 18 19 2 9 0 9)
  · change p=23 at hh; subst p
    exact fixed_23_18_false hf hg hm hn
  · change p=29 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 29 18 29 2 14 0 9)
  · change p=31 at hh; subst p
    exact fixed_31_18_false hf hg hm hn

#print axioms no_norm_cofactor_18

end Signed39.Contraction
