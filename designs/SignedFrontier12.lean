import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_11_12 : ℕ → Option QuotientInput
  | 17 => some ⟨17,3,8,0,44⟩
  | 29 => some ⟨29,3,14,0,44⟩
  | 31 => some ⟨31,3,15,0,44⟩
  | 37 => some ⟨37,11,3,0,12⟩
  | 41 => some ⟨41,3,4,0,44⟩
  | 67 => some ⟨67,3,11,0,44⟩
  | 87 => some ⟨3,11,1,0,12⟩
  | 173 => some ⟨173,3,86,0,44⟩
  | 293 => some ⟨293,3,146,0,44⟩
  | 393 => some ⟨3,11,1,0,12⟩
  | 527 => some ⟨17,3,8,0,44⟩
  | 879 => some ⟨3,11,1,0,12⟩
  | _ => none

private def keep_11_12 : List (ℕ × ℤ) := [(131,12),(131,1189),(263,1),(1319,1),(1319,14268)]

private theorem grid_11_12 : divisorGrid 11 12 77 qInputs_11_12 keep_11_12 := by decide +kernel

private theorem frontier_mixed_1441_144_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1441) : ¬∃ f : G → ℤ, IsSDS 144 12 f :=
  abelian_short_linear G 11 131 10 0 2 5 144 12 12 12 6 13
    ⟨⟨0,(-26),4,1⟩,[0,40,0,0,0,0,0,0,48,0,32],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1441_1321_1189 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1441) : ¬∃ f : G → ℤ, IsSDS 1321 1189 f :=
  abelian_short_linear G 11 131 10 0 2 5 1321 1189 12 119 6 13
    ⟨⟨109,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2893_133_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2893) : ¬∃ f : G → ℤ, IsSDS 133 1 f :=
  abelian_short_linear G 11 263 10 3 2 5 133 1 12 5 6 13
    ⟨⟨(-14760),(-1640),1271,0⟩,[0,0,2480,9840,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14509_133_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14509) : ¬∃ f : G → ℤ, IsSDS 133 1 f :=
  abelian_short_linear G 11 1319 10 0 2 5 133 1 12 11 6 13
    ⟨⟨(-413),0,20,(-7)⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14509_14400_14268 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14509) : ¬∃ f : G → ℤ, IsSDS 14400 14268 f :=
  abelian_short_linear G 11 1319 10 0 2 5 14400 14268 12 1308 6 13
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem fixed_11_12_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=11*m)
    (hm : 11 < m) (hn : k-l=(11:ℤ)*12) : False := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have row := endpoint_case (s:=12) hf hg hn (by decide) hm grid_11_12
  simp only [keep_11_12,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=144 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1441_144_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1321 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1441_1321_1189 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=133 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2893_133_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=133 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14509_133_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=14400 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14509_14400_14268 G hg ⟨f,hf⟩

private def qInputs_13_12 : ℕ → Option QuotientInput
  | 15 => some ⟨5,3,2,0,52⟩
  | 19 => some ⟨19,3,9,0,52⟩
  | 21 => some ⟨7,13,1,0,12⟩
  | 25 => some ⟨5,3,2,0,52⟩
  | 31 => some ⟨31,3,15,0,52⟩
  | 35 => some ⟨7,13,1,0,12⟩
  | 41 => some ⟨41,3,4,0,52⟩
  | 49 => some ⟨7,13,1,0,12⟩
  | 57 => some ⟨19,3,9,0,52⟩
  | 93 => some ⟨31,3,15,0,52⟩
  | 95 => some ⟨5,3,2,0,52⟩
  | 105 => some ⟨7,13,1,0,12⟩
  | 115 => some ⟨5,3,2,0,52⟩
  | 125 => some ⟨5,3,2,0,52⟩
  | 155 => some ⟨5,3,2,0,52⟩
  | 161 => some ⟨7,13,1,0,12⟩
  | 205 => some ⟨5,3,2,0,52⟩
  | 223 => some ⟨223,13,37,0,12⟩
  | 313 => some ⟨313,13,78,0,12⟩
  | 465 => some ⟨5,3,2,0,52⟩
  | 625 => some ⟨5,3,2,0,52⟩
  | 1561 => some ⟨7,13,1,0,12⟩
  | _ => none

private def keep_13_12 : List (ℕ × ℤ) := [(23,56),(23,95),(347,3),(347,4280),(1041,1),(1041,13300)]

private theorem grid_13_12 : divisorGrid 13 12 83 qInputs_13_12 keep_13_12 := by decide +kernel

private theorem frontier_mixed_299_212_56 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=299) : ¬∃ f : G → ℤ, IsSDS 212 56 f :=
  abelian_short_linear G 13 23 12 0 2 6 212 56 12 10 6 11
    ⟨⟨8,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_299_251_95 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=299) : ¬∃ f : G → ℤ, IsSDS 251 95 f :=
  abelian_short_linear G 13 23 12 0 2 6 251 95 12 13 6 11
    ⟨⟨(-4600),(-75),276,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4511_159_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4511) : ¬∃ f : G → ℤ, IsSDS 159 3 f :=
  abelian_short_linear G 13 347 12 1 2 6 159 3 12 9 6 11
    ⟨⟨(-1677),(-130),48,0⟩,[0,416,0,780,0,0,0,0,0,0,0,0,156],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4511_4436_4280 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4511) : ¬∃ f : G → ℤ, IsSDS 4436 4280 f :=
  abelian_short_linear G 13 347 12 0 2 6 4436 4280 12 338 6 11
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13533_157_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13533) : ¬∃ f : G → ℤ, IsSDS 157 1 f :=
  abelian_short_linear G 13 1041 12 1 2 6 157 1 12 9 6 11
    ⟨⟨(-543420064),(-21781980),14625540,0⟩,[0,174218220,0,130663665,0,0,0,0,0,0,0,0,130663665],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13533_13456_13300 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13533) : ¬∃ f : G → ℤ, IsSDS 13456 13300 f :=
  abelian_short_linear G 13 1041 12 0 2 6 13456 13300 12 1032 6 11
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem fixed_13_12_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=13*m)
    (hm : 13 < m) (hn : k-l=(13:ℤ)*12) : False := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have row := endpoint_case (s:=12) hf hg hn (by decide) hm grid_13_12
  simp only [keep_13_12,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=212 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_299_212_56 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=251 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_299_251_95 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=159 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4511_159_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4436 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4511_4436_4280 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=157 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13533_157_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=13456 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13533_13456_13300 G hg ⟨f,hf⟩

private def qInputs_23_12 : ℕ → Option QuotientInput
  | 25 => some ⟨5,3,2,0,92⟩
  | 31 => some ⟨31,23,5,0,12⟩
  | 33 => some ⟨3,23,1,0,12⟩
  | 39 => some ⟨3,23,1,0,12⟩
  | 51 => some ⟨3,23,1,0,12⟩
  | 55 => some ⟨5,3,2,0,92⟩
  | 65 => some ⟨5,3,2,0,92⟩
  | 73 => some ⟨73,3,6,0,92⟩
  | 75 => some ⟨3,23,1,0,12⟩
  | 89 => some ⟨89,3,44,0,92⟩
  | 125 => some ⟨5,3,2,0,92⟩
  | 143 => some ⟨13,23,3,0,12⟩
  | 155 => some ⟨5,3,2,0,92⟩
  | 163 => some ⟨163,23,9,0,12⟩
  | 165 => some ⟨3,23,1,0,12⟩
  | 195 => some ⟨3,23,1,0,12⟩
  | 223 => some ⟨223,3,111,0,92⟩
  | 275 => some ⟨5,3,2,0,92⟩
  | 365 => some ⟨5,3,2,0,92⟩
  | 617 => some ⟨617,3,308,0,92⟩
  | 825 => some ⟨3,23,1,0,12⟩
  | 1115 => some ⟨5,3,2,0,92⟩
  | 1851 => some ⟨3,23,1,0,12⟩
  | 2771 => some ⟨17,3,8,0,92⟩
  | _ => none

private def keep_23_12 : List (ℕ × ℤ) := [(563,1)]

private theorem grid_23_12 : divisorGrid 23 12 111 qInputs_23_12 keep_23_12 := by decide +kernel

private theorem frontier_mixed_12949_277_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12949) : ¬∃ f : G → ℤ, IsSDS 277 1 f :=
  abelian_short_linear G 23 563 16 3 1 0 277 1 12 5 1 1
    ⟨⟨(-3826854000),0,78805500,(-23165500)⟩,[3826854000,0,926620000,22748521,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,22748521,926620000,0],0⟩ hG (by decide +kernel)

private theorem fixed_23_12_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=23*m)
    (hm : 23 < m) (hn : k-l=(23:ℤ)*12) : False := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have row := endpoint_case (s:=12) hf hg hn (by decide) hm grid_23_12
  simp only [keep_23_12,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=277 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12949_277_1 G hg ⟨f,hf⟩

theorem no_norm_cofactor_12 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*12) (hs : ¬ p∣12) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=12) hf hd hn hs (by decide)
  have all : ∀ t : Fin 24, Nat.Prime t.val → 3≤t.val → ¬t.val∣12 → t.val=5 ∨ t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 12 5 3 2 0 4)
  · change p=7 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 7 12 7 3 3 0 4)
  · change p=11 at hh; subst p
    exact fixed_11_12_false hf hg hm hn
  · change p=13 at hh; subst p
    exact fixed_13_12_false hf hg hm hn
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 12 17 3 8 0 4)
  · change p=19 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 19 12 19 3 9 0 4)
  · change p=23 at hh; subst p
    exact fixed_23_12_false hf hg hm hn

#print axioms no_norm_cofactor_12

end Signed39.Contraction
