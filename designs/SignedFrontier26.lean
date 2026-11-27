import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_23_26 : ℕ → Option QuotientInput
  | 31 => some ⟨31,23,5,0,26⟩
  | 33 => some ⟨3,2,1,0,299⟩
  | 39 => some ⟨3,2,1,0,299⟩
  | 47 => some ⟨47,13,23,0,46⟩
  | 53 => some ⟨53,23,2,0,26⟩
  | 57 => some ⟨3,2,1,0,299⟩
  | 61 => some ⟨61,23,10,0,26⟩
  | 67 => some ⟨67,2,33,0,299⟩
  | 71 => some ⟨71,23,7,0,26⟩
  | 81 => some ⟨3,2,1,0,299⟩
  | 83 => some ⟨83,2,41,0,299⟩
  | 89 => some ⟨89,13,44,0,46⟩
  | 93 => some ⟨3,2,1,0,299⟩
  | 97 => some ⟨97,2,24,0,299⟩
  | 99 => some ⟨3,2,1,0,299⟩
  | 117 => some ⟨3,2,1,0,299⟩
  | 131 => some ⟨131,2,65,0,299⟩
  | 137 => some ⟨137,2,34,0,299⟩
  | 139 => some ⟨139,23,23,0,26⟩
  | 141 => some ⟨3,2,1,0,299⟩
  | 143 => some ⟨13,23,3,0,26⟩
  | 151 => some ⟨151,23,15,0,26⟩
  | 167 => some ⟨167,13,83,0,46⟩
  | 171 => some ⟨3,2,1,0,299⟩
  | 181 => some ⟨181,2,90,0,299⟩
  | 183 => some ⟨3,2,1,0,299⟩
  | 213 => some ⟨3,2,1,0,299⟩
  | 241 => some ⟨241,2,12,0,299⟩
  | 249 => some ⟨3,2,1,0,299⟩
  | 267 => some ⟨3,2,1,0,299⟩
  | 271 => some ⟨271,13,9,0,46⟩
  | 297 => some ⟨3,2,1,0,299⟩
  | 351 => some ⟨3,2,1,0,299⟩
  | 379 => some ⟨379,2,189,0,299⟩
  | 401 => some ⟨401,2,100,0,299⟩
  | 417 => some ⟨3,2,1,0,299⟩
  | 429 => some ⟨3,2,1,0,299⟩
  | 549 => some ⟨3,2,1,0,299⟩
  | 597 => some ⟨3,2,1,0,299⟩
  | 601 => some ⟨601,13,10,0,46⟩
  | 617 => some ⟨617,2,77,0,299⟩
  | 639 => some ⟨3,2,1,0,299⟩
  | 723 => some ⟨3,2,1,0,299⟩
  | 747 => some ⟨3,2,1,0,299⟩
  | 977 => some ⟨977,2,244,0,299⟩
  | 1101 => some ⟨3,2,1,0,299⟩
  | 1137 => some ⟨3,2,1,0,299⟩
  | 1287 => some ⟨3,2,1,0,299⟩
  | 1349 => some ⟨71,23,7,0,26⟩
  | 1529 => some ⟨11,2,5,0,299⟩
  | 1643 => some ⟨53,23,2,0,26⟩
  | 1837 => some ⟨11,2,5,0,299⟩
  | 1851 => some ⟨3,2,1,0,299⟩
  | 2241 => some ⟨3,2,1,0,299⟩
  | 2587 => some ⟨13,23,3,0,26⟩
  | 2757 => some ⟨3,2,1,0,299⟩
  | 2759 => some ⟨31,23,5,0,26⟩
  | 2931 => some ⟨3,2,1,0,299⟩
  | 3713 => some ⟨47,13,23,0,46⟩
  | 3861 => some ⟨3,2,1,0,299⟩
  | 4047 => some ⟨3,2,1,0,299⟩
  | 4587 => some ⟨3,2,1,0,299⟩
  | 5149 => some ⟨19,2,9,0,299⟩
  | 5553 => some ⟨3,2,1,0,299⟩
  | 6611 => some ⟨11,2,5,0,299⟩
  | 6621 => some ⟨3,2,1,0,299⟩
  | 7761 => some ⟨3,2,1,0,299⟩
  | 8277 => some ⟨3,2,1,0,299⟩
  | 10117 => some ⟨151,23,15,0,26⟩
  | 12141 => some ⟨3,2,1,0,299⟩
  | 14349 => some ⟨3,2,1,0,299⟩
  | _ => none

private def keep_23_26 : List (ℕ × ℤ) := [(79,94),(79,1083),(103,558),(103,627),(199,78),(199,3459),(367,3),(919,3),(2207,3),(2207,49982),(4783,3),(4783,108862)]

private theorem grid_23_26 : divisorGrid 23 26 245 qInputs_23_26 keep_23_26 := by decide +kernel

private theorem frontier_mixed_1817_692_94 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1817) : ¬∃ f : G → ℤ, IsSDS 692 94 f :=
  abelian_short_linear G 23 79 23 1 1 0 692 94 26 18 4 9
    ⟨⟨0,(-36313336),7622589,1116312⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,31930692,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1817_1681_1083 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1817) : ¬∃ f : G → ℤ, IsSDS 1681 1083 f :=
  abelian_short_linear G 23 79 23 0 1 0 1681 1083 26 61 4 9
    ⟨⟨4345,(-134),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2369_1156_558 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2369) : ¬∃ f : G → ℤ, IsSDS 1156 558 f :=
  abelian_short_linear G 23 103 23 0 1 0 1156 558 26 50 4 9
    ⟨⟨1938,(-151),60,1⟩,[132,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2369_1225_627 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2369) : ¬∃ f : G → ℤ, IsSDS 1225 627 f :=
  abelian_short_linear G 23 103 23 0 1 0 1225 627 26 53 4 9
    ⟨⟨3174,(-175),60,1⟩,[0,0,0,0,0,0,0,0,0,0,0,132,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4577_676_78 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4577) : ¬∃ f : G → ℤ, IsSDS 676 78 f :=
  abelian_short_linear G 23 199 23 1 1 0 676 78 26 26 4 9
    ⟨⟨(-8832),(-1541),629,24⟩,[0,0,0,0,0,0,0,0,0,0,5244,0,1288,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4577_4057_3459 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4577) : ¬∃ f : G → ℤ, IsSDS 4057 3459 f :=
  abelian_short_linear G 23 199 23 1 1 0 4057 3459 26 173 4 9
    ⟨⟨164,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8441_601_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8441) : ¬∃ f : G → ℤ, IsSDS 601 3 f :=
  abelian_short_linear G 23 367 23 8 1 0 601 3 26 7 4 9
    ⟨⟨(-6000),(-5250),848,159⟩,[6000,0,0,0,0,0,0,1500,0,0,0,0,0,6000,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_21137_601_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=21137) : ¬∃ f : G → ℤ, IsSDS 601 3 f :=
  abelian_short_linear G 23 919 23 7 1 0 601 3 26 11 4 9
    ⟨⟨(-77487),(-13340),2016,107⟩,[77487,0,19067,41952,0,6440,40779,0,28175,0,0,0,0,17112,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_50761_601_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=50761) : ¬∃ f : G → ℤ, IsSDS 601 3 f :=
  abelian_short_linear G 23 2207 23 4 1 0 601 3 26 17 4 9
    ⟨⟨0,(-10281),540,149⟩,[0,0,0,0,0,0,1242,0,7912,0,0,11362,5796,1012,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_50761_50580_49982 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=50761) : ¬∃ f : G → ℤ, IsSDS 50580 49982 f :=
  abelian_short_linear G 23 2207 23 0 1 0 50580 49982 26 2190 4 9
    ⟨⟨(-2207),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_110009_601_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=110009) : ¬∃ f : G → ℤ, IsSDS 601 3 f :=
  abelian_short_linear G 23 4783 23 0 1 0 601 3 26 25 4 9
    ⟨⟨0,(-621),27,4⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_110009_109460_108862 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=110009) : ¬∃ f : G → ℤ, IsSDS 109460 108862 f :=
  abelian_short_linear G 23 4783 23 0 1 0 109460 108862 26 4758 4 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem fixed_23_26_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=23*m)
    (hm : 23 < m) (hn : k-l=(23:ℤ)*26) : False := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have row := endpoint_case (s:=26) hf hg hn (by decide) hm grid_23_26
  simp only [keep_23_26,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=692 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1817_692_94 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1681 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1817_1681_1083 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1156 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2369_1156_558 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2369_1225_627 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=676 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4577_676_78 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4057 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4577_4057_3459 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=601 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8441_601_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=601 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_21137_601_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=601 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_50761_601_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=50580 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_50761_50580_49982 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=601 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_110009_601_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=109460 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_110009_109460_108862 G hg ⟨f,hf⟩

theorem no_norm_cofactor_26 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*26) (hs : ¬ p∣26) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=26) hf hd hn hs (by decide)
  have all : ∀ t : Fin 52, Nat.Prime t.val → 3≤t.val → ¬t.val∣26 → t.val=3 ∨ t.val=5 ∨ t.val=7 ∨ t.val=11 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 ∨ t.val=37 ∨ t.val=41 ∨ t.val=43 ∨ t.val=47 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 3 26 3 2 1 0 13)
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 26 5 2 2 0 13)
  · change p=7 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 7 26 7 13 1 0 2)
  · change p=11 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 11 26 11 2 5 0 13)
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 26 17 13 2 0 2)
  · change p=19 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 19 26 19 2 9 0 13)
  · change p=23 at hh; subst p
    exact fixed_23_26_false hf hg hm hn
  · change p=29 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 29 26 29 13 7 0 2)
  · change p=31 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 31 26 31 13 15 0 2)
  · change p=37 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 37 26 37 2 18 0 13)
  · change p=41 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 41 26 41 2 10 0 13)
  · change p=43 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 43 26 43 2 7 0 13)
  · change p=47 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 47 26 47 13 23 0 2)

#print axioms no_norm_cofactor_26

end Signed39.Contraction
