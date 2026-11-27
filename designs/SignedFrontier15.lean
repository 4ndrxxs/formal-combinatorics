import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_11_15 : ℕ → Option QuotientInput
  | 15 => some ⟨3,5,1,0,33⟩
  | 21 => some ⟨3,5,1,0,33⟩
  | 23 => some ⟨23,5,11,0,33⟩
  | 29 => some ⟨29,5,7,0,33⟩
  | 31 => some ⟨31,3,15,0,55⟩
  | 35 => some ⟨5,3,2,0,55⟩
  | 39 => some ⟨3,5,1,0,33⟩
  | 41 => some ⟨41,3,4,0,55⟩
  | 43 => some ⟨43,3,21,0,55⟩
  | 47 => some ⟨47,5,23,0,33⟩
  | 49 => some ⟨7,3,3,0,55⟩
  | 53 => some ⟨53,11,13,0,15⟩
  | 65 => some ⟨5,3,2,0,55⟩
  | 73 => some ⟨73,3,6,0,55⟩
  | 91 => some ⟨13,5,2,0,33⟩
  | 113 => some ⟨113,11,28,0,15⟩
  | 123 => some ⟨3,5,1,0,33⟩
  | 127 => some ⟨127,5,21,0,33⟩
  | 155 => some ⟨5,3,2,0,55⟩
  | 161 => some ⟨7,3,3,0,55⟩
  | 205 => some ⟨5,3,2,0,55⟩
  | 217 => some ⟨7,3,3,0,55⟩
  | 219 => some ⟨3,5,1,0,33⟩
  | 329 => some ⟨7,3,3,0,55⟩
  | 381 => some ⟨3,5,1,0,33⟩
  | 461 => some ⟨461,3,230,0,55⟩
  | 523 => some ⟨523,3,29,0,55⟩
  | 615 => some ⟨3,5,1,0,33⟩
  | 689 => some ⟨13,5,2,0,33⟩
  | 1085 => some ⟨5,3,2,0,55⟩
  | 1569 => some ⟨3,5,1,0,33⟩
  | 2141 => some ⟨2141,5,535,0,33⟩
  | _ => none

private def keep_11_15 : List (ℕ × ℤ) := [(131,4)]

private theorem grid_11_15 : divisorGrid 11 15 97 qInputs_11_15 keep_11_15 := by decide +kernel

private theorem frontier_mixed_1441_169_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1441) : ¬∃ f : G → ℤ, IsSDS 169 4 f :=
  abelian_short_linear G 11 131 12 4 1 0 169 4 15 7 7 19
    ⟨⟨0,(-106),21,5⟩,[0,0,0,0,0,6,0,0,24,0,0],0⟩ hG (by decide +kernel)

private theorem fixed_11_15_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=11*m)
    (hm : 11 < m) (hn : k-l=(11:ℤ)*15) : False := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have row := endpoint_case (s:=15) hf hg hn (by decide) hm grid_11_15
  simp only [keep_11_15,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=169 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1441_169_4 G hg ⟨f,hf⟩

theorem no_norm_cofactor_15 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*15) (hs : ¬ p∣15) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=15) hf hd hn hs (by decide)
  have all : ∀ t : Fin 30, Nat.Prime t.val → 3≤t.val → ¬t.val∣15 → t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh
  · change p=7 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 7 15 7 3 3 0 5)
  · change p=11 at hh; subst p
    exact fixed_11_15_false hf hg hm hn
  · change p=13 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 13 15 13 5 2 0 3)
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 15 17 3 8 0 5)
  · change p=19 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 19 15 19 3 9 0 5)
  · change p=23 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 23 15 23 5 11 0 3)
  · change p=29 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 29 15 29 5 7 0 3)

#print axioms no_norm_cofactor_15

end Signed39.Contraction
