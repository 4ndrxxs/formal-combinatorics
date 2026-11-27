import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_19_16 : ℕ → Option QuotientInput
  | 25 => some ⟨5,19,1,0,16⟩
  | 45 => some ⟨5,19,1,0,16⟩
  | 51 => some ⟨17,19,4,0,16⟩
  | 61 => some ⟨61,19,15,0,16⟩
  | 73 => some ⟨73,19,18,0,16⟩
  | 75 => some ⟨5,19,1,0,16⟩
  | 85 => some ⟨5,19,1,0,16⟩
  | 153 => some ⟨17,19,4,0,16⟩
  | 155 => some ⟨5,19,1,0,16⟩
  | 183 => some ⟨61,19,15,0,16⟩
  | 219 => some ⟨73,19,18,0,16⟩
  | 305 => some ⟨5,19,1,0,16⟩
  | 355 => some ⟨5,19,1,0,16⟩
  | 459 => some ⟨17,19,4,0,16⟩
  | 761 => some ⟨761,19,190,0,16⟩
  | 915 => some ⟨5,19,1,0,16⟩
  | 1065 => some ⟨5,19,1,0,16⟩
  | 2283 => some ⟨761,19,190,0,16⟩
  | 3195 => some ⟨5,19,1,0,16⟩
  | _ => none

private def keep_19_16 : List (ℕ × ℤ) := [(27,17),(31,5),(59,201),(59,372),(67,177),(67,500),(71,45),(71,900),(79,96),(79,837),(101,48),(101,1359),(103,36),(103,1461),(157,12),(157,2615),(167,4),(213,15),(213,3568),(303,16),(303,5165),(309,12),(309,5351),(471,4),(471,8573),(639,5),(639,11652),(927,4),(927,17085),(1523,1),(1523,28596),(4259,1),(4259,80352)]

private theorem grid_19_16 : divisorGrid 19 16 136 qInputs_19_16 keep_19_16 := by decide +kernel

private theorem frontier_mixed_513_321_17 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=513) : ¬∃ f : G → ℤ, IsSDS 321 17 f :=
  abelian_short_linear G 19 27 16 1 2 9 321 17 16 5 3 5
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_589_309_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=589) : ¬∃ f : G → ℤ, IsSDS 309 5 f :=
  abelian_short_linear G 19 31 16 1 2 9 309 5 16 3 3 5
    ⟨⟨(-1083),0,40,3⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1121_505_201 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1121) : ¬∃ f : G → ℤ, IsSDS 505 201 f :=
  abelian_short_linear G 19 59 16 0 2 9 505 201 16 25 3 5
    ⟨⟨(-27),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1121_676_372 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1121) : ¬∃ f : G → ℤ, IsSDS 676 372 f :=
  abelian_short_linear G 19 59 16 0 2 9 676 372 16 34 3 5
    ⟨⟨28,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1273_481_177 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1273) : ¬∃ f : G → ℤ, IsSDS 481 177 f :=
  abelian_short_linear G 19 67 16 0 2 9 481 177 16 25 3 5
    ⟨⟨(-27),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1273_804_500 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1273) : ¬∃ f : G → ℤ, IsSDS 804 500 f :=
  abelian_short_linear G 19 67 16 0 2 9 804 500 16 42 3 5
    ⟨⟨32,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1349_349_45 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1349) : ¬∃ f : G → ℤ, IsSDS 349 45 f :=
  abelian_short_linear G 19 71 16 1 2 9 349 45 16 13 3 5
    ⟨⟨0,(-5795),1518,163⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,6802,0,3192,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1349_1204_900 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1349) : ¬∃ f : G → ℤ, IsSDS 1204 900 f :=
  abelian_short_linear G 19 71 16 0 2 9 1204 900 16 58 3 5
    ⟨⟨50,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1501_400_96 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1501) : ¬∃ f : G → ℤ, IsSDS 400 96 f :=
  abelian_short_linear G 19 79 16 0 2 9 400 96 16 20 3 5
    ⟨⟨0,(-13),9,0⟩,[0,0,0,0,0,0,0,0,0,0,0,84,0,0,0,0,10,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1501_1141_837 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1501) : ¬∃ f : G → ℤ, IsSDS 1141 837 f :=
  abelian_short_linear G 19 79 16 0 2 9 1141 837 16 59 3 5
    ⟨⟨(-75),(-1),2,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1919_352_48 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1919) : ¬∃ f : G → ℤ, IsSDS 352 48 f :=
  abelian_short_linear G 19 101 16 1 2 9 352 48 16 16 3 5
    ⟨⟨(-78192828),(-23404656),4703336,678903⟩,[78192828,20745036,0,0,29255820,0,0,0,52660476,3723468,46809312,0,0,0,0,0,0,0,25532352],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1919_1663_1359 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1919) : ¬∃ f : G → ℤ, IsSDS 1663 1359 f :=
  abelian_short_linear G 19 101 16 0 2 9 1663 1359 16 85 3 5
    ⟨⟨7373,(-174),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1957_340_36 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1957) : ¬∃ f : G → ℤ, IsSDS 340 36 f :=
  abelian_short_linear G 19 103 16 1 2 9 340 36 16 14 3 5
    ⟨⟨0,(-646),168,17⟩,[0,0,0,608,0,0,0,0,0,0,0,0,0,0,0,0,608,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1957_1765_1461 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1957) : ¬∃ f : G → ℤ, IsSDS 1765 1461 f :=
  abelian_short_linear G 19 103 16 0 2 9 1765 1461 16 89 3 5
    ⟨⟨(-824),(-7),15,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2983_316_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2983) : ¬∃ f : G → ℤ, IsSDS 316 12 f :=
  abelian_short_linear G 19 157 16 3 2 9 316 12 16 10 3 5
    ⟨⟨(-9281728),(-1305243),213724,87780⟩,[9281728,0,0,0,0,0,0,0,0,0,1160216,0,2900540,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2983_2919_2615 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2983) : ¬∃ f : G → ℤ, IsSDS 2919 2615 f :=
  abelian_short_linear G 19 157 16 0 2 9 2919 2615 16 147 3 5
    ⟨⟨(-157),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3173_308_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3173) : ¬∃ f : G → ℤ, IsSDS 308 4 f :=
  abelian_short_linear G 19 167 16 4 2 9 308 4 16 6 3 5
    ⟨⟨0,(-63555),6021,2565⟩,[0,0,0,0,8474,0,0,0,0,0,0,0,0,0,0,0,59318,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4047_319_15 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4047) : ¬∃ f : G → ℤ, IsSDS 319 15 f :=
  abelian_short_linear G 19 213 16 1 2 9 319 15 16 13 3 5
    ⟨⟨(-2014),(-95),49,2⟩,[304,0,0,76,0,0,0,0,0,0,0,0,0,608,0,0,0,1140,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4047_3872_3568 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4047) : ¬∃ f : G → ℤ, IsSDS 3872 3568 f :=
  abelian_short_linear G 19 213 16 0 2 9 3872 3568 16 200 3 5
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5757_320_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5757) : ¬∃ f : G → ℤ, IsSDS 320 16 f :=
  abelian_short_linear G 19 303 16 0 2 9 320 16 16 16 3 5
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5757_5469_5165 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5757) : ¬∃ f : G → ℤ, IsSDS 5469 5165 f :=
  abelian_short_linear G 19 303 16 0 2 9 5469 5165 16 287 3 5
    ⟨⟨(-303),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5871_316_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5871) : ¬∃ f : G → ℤ, IsSDS 316 12 f :=
  abelian_short_linear G 19 309 16 1 2 9 316 12 16 14 3 5
    ⟨⟨0,(-18),11,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5871_5655_5351 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5871) : ¬∃ f : G → ℤ, IsSDS 5655 5351 f :=
  abelian_short_linear G 19 309 16 0 2 9 5655 5351 16 295 3 5
    ⟨⟨(-309),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8949_308_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8949) : ¬∃ f : G → ℤ, IsSDS 308 4 f :=
  abelian_short_linear G 19 471 16 3 2 9 308 4 16 10 3 5
    ⟨⟨0,0,128,(-63)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8949_8877_8573 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8949) : ¬∃ f : G → ℤ, IsSDS 8877 8573 f :=
  abelian_short_linear G 19 471 16 0 2 9 8877 8573 16 461 3 5
    ⟨⟨(-471),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12141_309_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12141) : ¬∃ f : G → ℤ, IsSDS 309 5 f :=
  abelian_short_linear G 19 639 16 1 2 9 309 5 16 13 3 5
    ⟨⟨3,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12141_11956_11652 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12141) : ¬∃ f : G → ℤ, IsSDS 11956 11652 f :=
  abelian_short_linear G 19 639 16 0 2 9 11956 11652 16 626 3 5
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_17613_308_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=17613) : ¬∃ f : G → ℤ, IsSDS 308 4 f :=
  abelian_short_linear G 19 927 16 1 2 9 308 4 16 14 3 5
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_17613_17389_17085 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=17613) : ¬∃ f : G → ℤ, IsSDS 17389 17085 f :=
  abelian_short_linear G 19 927 16 0 2 9 17389 17085 16 913 3 5
    ⟨⟨(-927),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28937_305_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28937) : ¬∃ f : G → ℤ, IsSDS 305 1 f :=
  abelian_short_linear G 19 1523 16 3 2 9 305 1 16 9 3 5
    ⟨⟨0,0,169,(-145)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28937_28900_28596 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28937) : ¬∃ f : G → ℤ, IsSDS 28900 28596 f :=
  abelian_short_linear G 19 1523 16 0 2 9 28900 28596 16 1514 3 5
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_80921_305_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=80921) : ¬∃ f : G → ℤ, IsSDS 305 1 f :=
  abelian_short_linear G 19 4259 16 0 2 9 305 1 16 15 3 5
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_80921_80656_80352 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=80921) : ¬∃ f : G → ℤ, IsSDS 80656 80352 f :=
  abelian_short_linear G 19 4259 16 0 2 9 80656 80352 16 4244 3 5
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_19_16_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=19*m)
    (hm : 19 < m) (hn : k-l=(19:ℤ)*16) : False := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  have row := endpoint_case (s:=16) hf hg hn (by decide) hm grid_19_16
  simp only [keep_19_16,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=321 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_513_321_17 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=309 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_589_309_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=505 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1121_505_201 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=676 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1121_676_372 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=481 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1273_481_177 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=804 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1273_804_500 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=349 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1349_349_45 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1204 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1349_1204_900 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=400 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1501_400_96 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1141 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1501_1141_837 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=352 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1919_352_48 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1663 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1919_1663_1359 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=340 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1957_340_36 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1765 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1957_1765_1461 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=316 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2983_316_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2919 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2983_2919_2615 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=308 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3173_308_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=319 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4047_319_15 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3872 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4047_3872_3568 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=320 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5757_320_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5469 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5757_5469_5165 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=316 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5871_316_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5655 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5871_5655_5351 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=308 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8949_308_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=8877 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8949_8877_8573 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=309 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12141_309_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=11956 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12141_11956_11652 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=308 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_17613_308_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=17389 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_17613_17389_17085 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=305 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28937_305_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=28900 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28937_28900_28596 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=305 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_80921_305_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=80656 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_80921_80656_80352 G hg ⟨f,hf⟩

end Signed39.Contraction
