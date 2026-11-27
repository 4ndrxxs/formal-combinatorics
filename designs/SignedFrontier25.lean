import Signed25Prime3
import Signed25Prime7
import Signed25Prime11
import Signed25Prime13
import Signed25Prime17
import Signed25Prime19
import Signed25Prime23
import Signed25Prime29
import Signed25Prime31
import Signed25Prime37
import Signed25Prime41
import Signed25Prime43
import Signed25Prime47

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_norm_cofactor_25 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*25) (hs : ¬ p∣25) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=25) hf hd hn hs (by decide)
  have all : ∀ t : Fin 50, Nat.Prime t.val → 3≤t.val → ¬t.val∣25 → t.val=3 ∨ t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 ∨ t.val=37 ∨ t.val=41 ∨ t.val=43 ∨ t.val=47 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact fixed_3_25_false hf hg hm hn
  · change p=7 at hh; subst p
    exact fixed_7_25_false hf hg hm hn
  · change p=11 at hh; subst p
    exact fixed_11_25_false hf hg hm hn
  · change p=13 at hh; subst p
    exact fixed_13_25_false hf hg hm hn
  · change p=17 at hh; subst p
    exact fixed_17_25_false hf hg hm hn
  · change p=19 at hh; subst p
    exact fixed_19_25_false hf hg hm hn
  · change p=23 at hh; subst p
    exact fixed_23_25_false hf hg hm hn
  · change p=29 at hh; subst p
    exact fixed_29_25_false hf hg hm hn
  · change p=31 at hh; subst p
    exact fixed_31_25_false hf hg hm hn
  · change p=37 at hh; subst p
    exact fixed_37_25_false hf hg hm hn
  · change p=41 at hh; subst p
    exact fixed_41_25_false hf hg hm hn
  · change p=43 at hh; subst p
    exact fixed_43_25_false hf hg hm hn
  · change p=47 at hh; subst p
    exact fixed_47_25_false hf hg hm hn

#print axioms no_norm_cofactor_25

end Signed39.Contraction
