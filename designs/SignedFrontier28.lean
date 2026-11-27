import Signed28Prime3
import Signed28Prime19
import Signed28Prime29
import Signed28Prime31
import Signed28Prime37
import Signed28Prime47

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_norm_cofactor_28 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*28) (hs : ¬ p∣28) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=28) hf hd hn hs (by decide)
  have all : ∀ t : Fin 56, Nat.Prime t.val → 3≤t.val → ¬t.val∣28 → t.val=3 ∨ t.val=5 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 ∨ t.val=37 ∨ t.val=41 ∨ t.val=43 ∨ t.val=47 ∨ t.val=53 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact fixed_3_28_false hf hg hm hn
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 28 5 7 2 0 4)
  · change p=11 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 11 28 11 7 5 0 4)
  · change p=13 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 13 28 13 7 6 0 4)
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 28 17 7 8 0 4)
  · change p=19 at hh; subst p
    exact fixed_19_28_false hf hg hm hn
  · change p=23 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 23 28 23 7 11 0 4)
  · change p=29 at hh; subst p
    exact fixed_29_28_false hf hg hm hn
  · change p=31 at hh; subst p
    exact fixed_31_28_false hf hg hm hn
  · change p=37 at hh; subst p
    exact fixed_37_28_false hf hg hm hn
  · change p=41 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 41 28 41 7 20 0 4)
  · change p=43 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 43 28 43 7 3 0 4)
  · change p=47 at hh; subst p
    exact fixed_47_28_false hf hg hm hn
  · change p=53 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 53 28 53 7 13 0 4)

#print axioms no_norm_cofactor_28

end Signed39.Contraction
