import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_19_17 : ℕ → Option QuotientInput
  | 23 => some ⟨23,17,11,0,19⟩
  | 29 => some ⟨29,17,2,0,19⟩
  | 37 => some ⟨37,17,18,0,19⟩
  | 41 => some ⟨41,17,20,0,19⟩
  | 49 => some ⟨7,17,3,0,19⟩
  | 77 => some ⟨7,17,3,0,19⟩
  | 109 => some ⟨109,17,18,0,19⟩
  | 119 => some ⟨7,17,3,0,19⟩
  | 131 => some ⟨131,19,13,0,17⟩
  | 161 => some ⟨7,17,3,0,19⟩
  | 163 => some ⟨163,17,27,0,19⟩
  | 269 => some ⟨269,17,134,0,19⟩
  | 287 => some ⟨7,17,3,0,19⟩
  | 337 => some ⟨337,17,56,0,19⟩
  | 391 => some ⟨17,19,4,0,17⟩
  | 457 => some ⟨457,17,19,0,19⟩
  | 667 => some ⟨29,17,2,0,19⟩
  | 761 => some ⟨761,17,190,0,19⟩
  | 1141 => some ⟨7,17,3,0,19⟩
  | 1199 => some ⟨11,17,5,0,19⟩
  | 1597 => some ⟨1597,19,399,0,17⟩
  | 1883 => some ⟨7,17,3,0,19⟩
  | 2129 => some ⟨2129,17,133,0,19⟩
  | 2737 => some ⟨7,17,3,0,19⟩
  | 3707 => some ⟨11,17,5,0,19⟩
  | 4847 => some ⟨131,19,13,0,17⟩
  | _ => none

private def keep_19_17 : List (ℕ × ℤ) := [(59,1),(67,137),(67,574),(229,2),(2719,1),(2719,51206)]

private theorem grid_19_17 : divisorGrid 19 17 144 qInputs_19_17 keep_19_17 := by decide +kernel

private def types_frontier_mixed_1121_324_1 : List RowType := [((-15),27),((-14),22),((-13),37),((-12),34),((-11),51),((-10),50),((-9),31),((-8),32),((-7),53),((-6),56),((-5),41),((-4),46),((-3),33),((-2),40),((-1),29),(0,0),(0,38),(1,29),(2,40),(3,33),(4,46),(5,41),(6,56),(7,53),(8,32),(9,31),(10,50),(11,51),(12,34),(13,37),(14,22),(15,27),(16,52),(18,48),(19,57)]
private def stage_0_frontier_mixed_1121_324_1 : Stage := [
  (((-15),27),⟨⟨(-62776),0,0,532⟩,[62776,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],9⟩),
  (((-14),22),⟨⟨(-564984),(-43719),8201,6986⟩,[564984,0,0,262314,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],24⟩),
  (((-13),37),⟨⟨(-1611998),0,24308,3996⟩,[1611998,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],97⟩),
  (((-12),34),⟨⟨(-6244578000),(-547770000),66309000,73150000⟩,[6244578000,0,0,3286620000,328662000,0,0,328662000,0,0,0,0,0,0,0,0,0,0,0],602547⟩),
  (((-11),51),⟨⟨(-51566),0,590,370⟩,[51566,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],3⟩),
  (((-10),50),⟨⟨(-257830),0,4956,1246⟩,[257830,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],9⟩),
  (((-9),31),⟨⟨(-720626),(-1062),10797,1219⟩,[720626,2124,0,45548,49678,0,0,0,16992,0,0,0,0,0,0,41182,39176,0,0],31⟩),
  (((-8),32),⟨⟨(-1140057),0,25960,1441⟩,[1140057,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],36⟩),
  (((-7),53),⟨⟨(-2159046),0,63425,2041⟩,[2159046,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],22⟩),
  (((-6),56),⟨⟨(-139004),0,1239,473⟩,[139004,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],12⟩),
  (((-5),41),⟨⟨(-139004),0,3717,279⟩,[139004,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],2⟩),
  (((-4),46),⟨⟨(-468578),0,8024,244⟩,[468578,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],39⟩),
  (((-3),33),⟨⟨(-2029010),0,38055,4865⟩,[2029010,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],57⟩),
  (((-2),40),⟨⟨0,(-3363),0,171⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((2,40),⟨⟨0,(-3363),0,171⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((3,33),⟨⟨(-2029010),0,38055,4865⟩,[2029010,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],57⟩),
  ((4,46),⟨⟨(-468578),0,8024,244⟩,[468578,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],39⟩),
  ((5,41),⟨⟨(-139004),0,3717,279⟩,[139004,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],2⟩),
  ((6,56),⟨⟨(-139004),0,1239,473⟩,[139004,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],12⟩),
  ((7,53),⟨⟨(-2159046),0,63425,2041⟩,[2159046,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],22⟩),
  ((8,32),⟨⟨(-1140057),0,25960,1441⟩,[1140057,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],36⟩),
  ((9,31),⟨⟨(-720626),(-1062),10797,1219⟩,[720626,2124,0,45548,49678,0,0,0,16992,0,0,0,0,0,0,41182,39176,0,0],31⟩),
  ((10,50),⟨⟨(-257830),0,4956,1246⟩,[257830,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],9⟩),
  ((11,51),⟨⟨(-51566),0,590,370⟩,[51566,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],3⟩),
  ((12,34),⟨⟨(-484272),0,0,1938⟩,[484272,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],91⟩),
  ((13,37),⟨⟨(-1611998),0,24308,3996⟩,[1611998,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],97⟩),
  ((14,22),⟨⟨(-750880000),0,0,2855625⟩,[750880000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],316784⟩),
  ((15,27),⟨⟨(-62776),0,0,532⟩,[62776,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],9⟩),
  ((16,52),⟨⟨(-58292),0,885,707⟩,[58292,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],2⟩),
  ((18,48),⟨⟨(-1047014),0,23010,2156⟩,[1047014,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],23⟩),
  ((19,57),⟨⟨(-456),(-19),15,2⟩,[456,38,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩)]
private theorem frontier_mixed_1121_324_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1121) : ¬∃ f : G → ℤ, IsSDS 324 1 f :=
  abelian_short_mixed G 19 59 17 1 1 0 324 1 17 2 14 25 28 9
    types_frontier_mixed_1121_324_1 [stage_0_frontier_mixed_1121_324_1] ⟨⟨1,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1273_460_137 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1273) : ¬∃ f : G → ℤ, IsSDS 460 137 f :=
  abelian_short_linear G 19 67 17 1 1 0 460 137 17 22 14 25
    ⟨⟨0,(-1349),336,31⟩,[0,1140,0,0,0,0,0,0,2736,0,0,0,0,0,0,0,0,0,798],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1273_897_574 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1273) : ¬∃ f : G → ℤ, IsSDS 897 574 f :=
  abelian_short_linear G 19 67 17 1 1 0 897 574 17 45 14 25
    ⟨⟨0,0,1521,(-59)⟩,[0,0,0,0,0,0,0,0,0,28424,0,0,0,8702,0,0,15998,6498,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4351_325_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4351) : ¬∃ f : G → ℤ, IsSDS 325 2 f :=
  abelian_short_linear G 19 229 17 6 1 0 325 2 17 5 14 25
    ⟨⟨0,(-455238632),74433888,11068445⟩,[0,0,0,0,0,138648600,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_51661_324_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=51661) : ¬∃ f : G → ℤ, IsSDS 324 1 f :=
  abelian_short_linear G 19 2719 17 2 1 0 324 1 17 12 14 25
    ⟨⟨0,(-4427),306,37⟩,[0,0,0,0,0,0,0,1330,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_51661_51529_51206 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=51661) : ¬∃ f : G → ℤ, IsSDS 51529 51206 f :=
  abelian_short_linear G 19 2719 17 0 1 0 51529 51206 17 2707 14 25
    ⟨⟨(-2719),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem fixed_19_17_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=19*m)
    (hm : 19 < m) (hn : k-l=(19:ℤ)*17) : False := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  have row := endpoint_case (s:=17) hf hg hn (by decide) hm grid_19_17
  simp only [keep_19_17,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=324 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1121_324_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=460 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1273_460_137 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=897 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1273_897_574 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=325 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4351_325_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=324 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_51661_324_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=51529 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_51661_51529_51206 G hg ⟨f,hf⟩

theorem no_norm_cofactor_17 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*17) (hs : ¬ p∣17) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=17) hf hd hn hs (by decide)
  have all : ∀ t : Fin 34, Nat.Prime t.val → 3≤t.val → ¬t.val∣17 → t.val=3 ∨ t.val=5 ∨ t.val=7 ∨ t.val=11 ∨ t.val=13 ∨ t.val=19 ∨ t.val=23 ∨ t.val=29 ∨ t.val=31 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 3 17 3 17 1 0 1)
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 17 5 17 2 0 1)
  · change p=7 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 7 17 7 17 3 0 1)
  · change p=11 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 11 17 11 17 5 0 1)
  · change p=13 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 13 17 13 17 3 0 1)
  · change p=19 at hh; subst p
    exact fixed_19_17_false hf hg hm hn
  · change p=23 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 23 17 23 17 11 0 1)
  · change p=29 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 29 17 29 17 2 0 1)
  · change p=31 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 31 17 31 17 15 0 1)

#print axioms no_norm_cofactor_17

end Signed39.Contraction
