import Signed27Prime11
import Signed27Prime13
import Signed27Prime23
import Signed27Prime47

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_norm_cofactor_27 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*27) (hs : ¬ p∣27) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=27) hf hd hn hs (by decide)
  have all : ∀ t : Fin 54, Nat.Prime t.val → 3≤t.val → ¬t.val∣27 → t.val=5 ∨ t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 ∨ t.val=37 ∨ t.val=41 ∨ t.val=43 ∨ t.val=47 ∨ t.val=53 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 27 5 3 2 1 1)
  · change p=7 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 7 27 7 3 3 1 1)
  · change p=11 at hh; subst p
    exact fixed_11_27_false hf hg hm hn
  · change p=13 at hh; subst p
    exact fixed_13_27_false hf hg hm hn
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 27 17 3 8 1 1)
  · change p=19 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 19 27 19 3 9 1 1)
  · change p=23 at hh; subst p
    exact fixed_23_27_false hf hg hm hn
  · change p=29 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 29 27 29 3 14 1 1)
  · change p=31 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 31 27 31 3 15 1 1)
  · change p=37 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 37 27 37 3 9 1 1)
  · change p=41 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 41 27 41 3 4 1 1)
  · change p=43 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 43 27 43 3 21 1 1)
  · change p=47 at hh; subst p
    exact fixed_47_27_false hf hg hm hn
  · change p=53 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 53 27 53 3 26 1 1)

#print axioms no_norm_cofactor_27

end Signed39.Contraction
