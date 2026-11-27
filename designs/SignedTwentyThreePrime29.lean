import SignedTwentyThreeGrid29
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0



private def types_frontier_mixed_1421_676_9 : List RowType := [((-15),33),((-12),42),((-10),34),((-8),38),((-1),45),(0,0),(1,45),(8,38),(10,34),(12,42),(15,33)]
private def stage_0_frontier_mixed_1421_676_9 : Stage := [
  (((-15),33),⟨⟨(-126672),(-24766),0,2146⟩,[126672,0,0,0,0,0,0,0,105154,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],11⟩),
  (((-12),42),⟨⟨0,0,(-370),120⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  (((-10),34),⟨⟨0,0,(-390),150⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  (((-1),45),⟨⟨0,0,(-14161),(-117)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],37⟩),
  ((1,45),⟨⟨0,0,(-14161),(-117)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],37⟩),
  ((10,34),⟨⟨0,0,(-390),150⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((12,42),⟨⟨0,0,(-370),120⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((15,33),⟨⟨(-926898),(-14210),0,4640⟩,[926898,0,0,0,0,0,0,0,227360,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],69⟩)]
private theorem frontier_mixed_1421_676_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1421) : ¬∃ f : G → ℤ, IsSDS 676 9 f :=
  abelian_short_mixed G 29 49 25 1 1 0 676 9 23 4 12 19 22 13
    types_frontier_mixed_1421_676_9 [stage_0_frontier_mixed_1421_676_9] ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1943_1006_339 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1943) : ¬∃ f : G → ℤ, IsSDS 1006 339 f :=
  abelian_short_linear G 29 67 25 1 1 0 1006 339 23 28 12 19
    ⟨⟨0,(-406),111,7⟩,[0,1218,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1943_1325_658 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1943) : ¬∃ f : G → ℤ, IsSDS 1325 658 f :=
  abelian_short_linear G 29 67 25 0 1 0 1325 658 23 39 12 19
    ⟨⟨0,0,121,(-7)⟩,[0,1218,0,0,0,348,0,0,3654,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2407_709_42 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2407) : ¬∃ f : G → ℤ, IsSDS 709 42 f :=
  abelian_short_linear G 29 83 25 1 1 0 709 42 23 11 12 19
    ⟨⟨0,(-781450254),100164103,32005098⟩,[0,0,0,0,0,0,0,0,0,0,0,1222550901,0,0,868312224,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2987_758_91 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2987) : ¬∃ f : G → ℤ, IsSDS 758 91 f :=
  abelian_short_linear G 29 103 25 1 1 0 758 91 23 18 12 19
    ⟨⟨0,(-1131),270,23⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1566,0,0,4698,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2987_2701_2034 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2987) : ¬∃ f : G → ℤ, IsSDS 2701 2034 f :=
  abelian_short_linear G 29 103 25 0 1 0 2701 2034 23 85 12 19
    ⟨⟨1075320,(-41122),7095,229⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,89958,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3103_850_183 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3103) : ¬∃ f : G → ℤ, IsSDS 850 183 f :=
  abelian_short_linear G 29 107 25 1 1 0 850 183 23 26 12 19
    ⟨⟨0,(-6351),1386,125⟩,[0,0,0,0,0,0,0,0,0,0,3886,0,0,0,0,0,0,0,0,0,0,0,0,0,8352,7192,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3103_2445_1778 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3103) : ¬∃ f : G → ℤ, IsSDS 2445 1778 f :=
  abelian_short_linear G 29 107 25 0 1 0 2445 1778 23 81 12 19
    ⟨⟨0,(-65015910),48105036,0⟩,[0,0,0,0,90489980,203602455,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,565539408,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5017_748_81 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5017) : ¬∃ f : G → ℤ, IsSDS 748 81 f :=
  abelian_short_linear G 29 173 25 1 1 0 748 81 23 22 12 19
    ⟨⟨0,(-17719),3825,316⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45298,6090,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5017_4489_3822 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5017) : ¬∃ f : G → ℤ, IsSDS 4489 3822 f :=
  abelian_short_linear G 29 173 25 0 1 0 4489 3822 23 151 12 19
    ⟨⟨(-1474998),0,12505,(-23)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,26100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5771_709_42 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5771) : ¬∃ f : G → ℤ, IsSDS 709 42 f :=
  abelian_short_linear G 29 199 25 3 1 0 709 42 23 17 12 19
    ⟨⟨0,(-522),81,13⟩,[0,0,0,0,0,0,0,0,0,0,0,1334,0,0,0,0,0,0,0,0,0,0,0,1160,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5771_5494_4827 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5771) : ¬∃ f : G → ℤ, IsSDS 5494 4827 f :=
  abelian_short_linear G 29 199 25 0 1 0 5494 4827 23 182 12 19
    ⟨⟨(-199),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6583_718_51 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6583) : ¬∃ f : G → ℤ, IsSDS 718 51 f :=
  abelian_short_linear G 29 227 25 2 1 0 718 51 23 20 12 19
    ⟨⟨0,(-14297),1950,419⟩,[0,0,0,0,0,0,0,0,0,0,26970,0,0,0,0,0,0,0,0,0,0,16008,6438,19430,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6583_6141_5474 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6583) : ¬∃ f : G → ℤ, IsSDS 6141 5474 f :=
  abelian_short_linear G 29 227 25 0 1 0 6141 5474 23 207 12 19
    ⟨⟨(-2545578),(-24830),36045,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_16849_673_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=16849) : ¬∃ f : G → ℤ, IsSDS 673 6 f :=
  abelian_short_linear G 29 581 25 6 1 0 673 6 23 11 12 19
    ⟨⟨(-11308),(-1029),174,13⟩,[11308,2058,2526,2620,2340,1686,658,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20909_680_13 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20909) : ¬∃ f : G → ℤ, IsSDS 680 13 f :=
  abelian_short_linear G 29 721 25 2 1 0 680 13 23 18 12 19
    ⟨⟨(-2020),(-729),42,19⟩,[2020,0,0,1390,0,276,0,0,0,280,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20909_20545_19878 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20909) : ¬∃ f : G → ℤ, IsSDS 20545 19878 f :=
  abelian_short_linear G 29 721 25 0 1 0 20545 19878 23 703 12 19
    ⟨⟨(-721),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_40397_673_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=40397) : ¬∃ f : G → ℤ, IsSDS 673 6 f :=
  abelian_short_linear G 29 1393 25 3 1 0 673 6 23 17 12 19
    ⟨⟨0,0,49,(-165)⟩,[0,0,0,0,0,0,0,0,1740,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_40397_40084_39417 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=40397) : ¬∃ f : G → ℤ, IsSDS 40084 39417 f :=
  abelian_short_linear G 29 1393 25 0 1 0 40084 39417 23 1376 12 19
    ⟨⟨(-1393),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_29_23_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=29*m)
    (hm : 29 < m) (hn : k-l=(29:ℤ)*23) : False := by
  let : Fact (Nat.Prime 29) := ⟨by decide⟩
  have row := endpoint_case (s:=23) hf hg hn (by decide) hm grid_29_23
  simp only [keep_29_23,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=676 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1421_676_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1006 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1943_1006_339 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1325 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1943_1325_658 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=709 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2407_709_42 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=758 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2987_758_91 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2701 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2987_2701_2034 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=850 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3103_850_183 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2445 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3103_2445_1778 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=748 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5017_748_81 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4489 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5017_4489_3822 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=709 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5771_709_42 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5494 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5771_5494_4827 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=718 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6583_718_51 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6141 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6583_6141_5474 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=673 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_16849_673_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=680 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20909_680_13 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=20545 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20909_20545_19878 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=673 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_40397_673_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=40084 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_40397_40084_39417 G hg ⟨f,hf⟩

end Signed39.Contraction
