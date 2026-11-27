import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification
import Signed95SixtyOne

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_5_11 : ℕ → Option QuotientInput
  | 17 => some ⟨17,5,8,0,11⟩
  | 23 => some ⟨23,5,11,0,11⟩
  | 27 => some ⟨3,5,1,0,11⟩
  | 33 => some ⟨3,5,1,0,11⟩
  | 39 => some ⟨3,5,1,0,11⟩
  | 47 => some ⟨47,5,23,0,11⟩
  | 51 => some ⟨3,5,1,0,11⟩
  | 57 => some ⟨3,5,1,0,11⟩
  | 69 => some ⟨3,5,1,0,11⟩
  | 99 => some ⟨3,5,1,0,11⟩
  | 103 => some ⟨103,5,51,0,11⟩
  | 117 => some ⟨3,5,1,0,11⟩
  | 163 => some ⟨163,5,27,0,11⟩
  | 169 => some ⟨13,5,2,0,11⟩
  | 197 => some ⟨197,5,98,0,11⟩
  | 297 => some ⟨3,5,1,0,11⟩
  | 309 => some ⟨3,5,1,0,11⟩
  | 489 => some ⟨3,5,1,0,11⟩
  | _ => none

private def keep_5_11 : List (ℕ × ℤ) := [(11,(-1)),(19,6)]

private theorem grid_5_11 : divisorGrid 5 11 47 qInputs_5_11 keep_5_11 := by decide +kernel

private theorem frontier_mixed_55_54_neg1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=55) : ¬∃ f : G → ℤ, IsSDS 54 (-1) f :=
  abelian_short_linear G 5 11 6 1 1 0 54 (-1) 11 0 3 13
    ⟨⟨34,0,(-3),(-1)⟩,[0,0,2,2,0],0⟩ hG (by decide +kernel)

private theorem fixed_5_11_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=5*m)
    (hm : 5 < m) (hn : k-l=(5:ℤ)*11) : False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have row := endpoint_case (s:=11) hf hg hn (by decide) hm grid_5_11
  simp only [keep_5_11,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=54 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_55_54_neg1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=61 := by omega
    rw [hk,hL] at hf
    exact Signed39.NinetyFiveSixtyOne.no_abelian_95_61_6 G hg ⟨f,hf⟩

private def qInputs_7_11 : ℕ → Option QuotientInput
  | 11 => some ⟨11,7,5,0,11⟩
  | 13 => some ⟨13,7,6,0,11⟩
  | 17 => some ⟨17,7,8,0,11⟩
  | 23 => some ⟨23,7,11,0,11⟩
  | 37 => some ⟨37,11,3,0,7⟩
  | 41 => some ⟨41,7,20,0,11⟩
  | 53 => some ⟨53,7,13,0,11⟩
  | 101 => some ⟨101,7,50,0,11⟩
  | 209 => some ⟨11,7,5,0,11⟩
  | 241 => some ⟨241,11,24,0,7⟩
  | 437 => some ⟨23,7,11,0,11⟩
  | 689 => some ⟨13,7,6,0,11⟩
  | _ => none

private def keep_7_11 : List (ℕ × ℤ) := [(19,23),(19,44),(83,4),(83,487),(139,4),(139,851)]

private theorem grid_7_11 : divisorGrid 7 11 56 qInputs_7_11 keep_7_11 := by decide +kernel

private theorem frontier_mixed_133_100_23 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=133) : ¬∃ f : G → ℤ, IsSDS 100 23 f :=
  abelian_short_linear G 7 19 8 1 1 0 100 23 11 8 1 3
    ⟨⟨126,0,(-9),(-1)⟩,[0,28,0,0,112,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_133_121_44 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=133) : ¬∃ f : G → ℤ, IsSDS 121 44 f :=
  abelian_short_linear G 7 19 8 1 1 0 121 44 11 11 1 3
    ⟨⟨13,0,(-1),0⟩,[0,0,0,0,0,6,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_581_81_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=581) : ¬∃ f : G → ℤ, IsSDS 81 4 f :=
  abelian_short_linear G 7 83 8 2 1 0 81 4 11 7 1 3
    ⟨⟨0,(-35),9,2⟩,[0,0,0,42,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_581_564_487 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=581) : ¬∃ f : G → ℤ, IsSDS 564 487 f :=
  abelian_short_linear G 7 83 8 1 1 0 564 487 11 76 1 3
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,1],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_973_81_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=973) : ¬∃ f : G → ℤ, IsSDS 81 4 f :=
  abelian_short_linear G 7 139 8 1 1 0 81 4 11 9 1 3
    ⟨⟨0,(-89404),10416,5643⟩,[0,0,52080,59024,102858,10416,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_973_928_851 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=973) : ¬∃ f : G → ℤ, IsSDS 928 851 f :=
  abelian_short_linear G 7 139 8 1 1 0 928 851 11 130 1 3
    ⟨⟨125,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem fixed_7_11_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=7*m)
    (hm : 7 < m) (hn : k-l=(7:ℤ)*11) : False := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have row := endpoint_case (s:=11) hf hg hn (by decide) hm grid_7_11
  simp only [keep_7_11,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=100 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_133_100_23 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=121 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_133_121_44 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=81 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_581_81_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=564 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_581_564_487 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=81 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_973_81_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=928 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_973_928_851 G hg ⟨f,hf⟩

private def qInputs_19_11 : ℕ → Option QuotientInput
  | 23 => some ⟨23,11,11,0,19⟩
  | 25 => some ⟨5,19,1,0,11⟩
  | 29 => some ⟨29,11,14,0,19⟩
  | 41 => some ⟨41,11,20,0,19⟩
  | 47 => some ⟨47,11,23,0,19⟩
  | 65 => some ⟨5,19,1,0,11⟩
  | 109 => some ⟨109,19,18,0,11⟩
  | 115 => some ⟨5,19,1,0,11⟩
  | 143 => some ⟨11,19,5,0,11⟩
  | 191 => some ⟨191,11,19,0,19⟩
  | 241 => some ⟨241,11,24,0,19⟩
  | 293 => some ⟨293,11,146,0,19⟩
  | 673 => some ⟨673,11,336,0,19⟩
  | 1205 => some ⟨5,19,1,0,11⟩
  | 1889 => some ⟨1889,11,944,0,19⟩
  | _ => none

private def keep_19_11 : List (ℕ × ℤ) := []

private theorem grid_19_11 : divisorGrid 19 11 92 qInputs_19_11 keep_19_11 := by decide +kernel

private theorem fixed_19_11_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=19*m)
    (hm : 19 < m) (hn : k-l=(19:ℤ)*11) : False := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  have row := endpoint_case (s:=11) hf hg hn (by decide) hm grid_19_11
  simp [keep_19_11] at row


theorem no_norm_cofactor_11 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*11) (hs : ¬ p∣11) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=11) hf hd hn hs (by decide)
  have all : ∀ t : Fin 22, Nat.Prime t.val → 3≤t.val → ¬t.val∣11 → t.val=3 ∨ t.val=5 ∨ t.val=7 ∨ t.val=13 ∨ t.val=17 ∨ t.val=19 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 3 11 3 11 1 0 1)
  · change p=5 at hh; subst p
    exact fixed_5_11_false hf hg hm hn
  · change p=7 at hh; subst p
    exact fixed_7_11_false hf hg hm hn
  · change p=13 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 13 11 13 11 6 0 1)
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 11 17 11 8 0 1)
  · change p=19 at hh; subst p
    exact fixed_19_11_false hf hg hm hn

#print axioms no_norm_cofactor_11

end Signed39.Contraction
