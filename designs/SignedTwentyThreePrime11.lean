import Signed473
import SignedTwentyThreeCase539W310
import SignedTwentyThreeCase869W280
import SignedTwentyThreeCase913W372
import SignedTwentyThreeCase913W625
import SignedTwentyThreeCase1177W312
import SignedTwentyThreeCase1463W274
import SignedTwentyThreeCase2497W256
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_11_23 : ℕ → Option QuotientInput
  | 23 => some ⟨23,11,11,0,23⟩
  | 31 => some ⟨31,23,5,0,11⟩
  | 47 => some ⟨47,11,23,0,23⟩
  | 51 => some ⟨3,11,1,0,23⟩
  | 57 => some ⟨3,11,1,0,23⟩
  | 59 => some ⟨59,11,29,0,23⟩
  | 61 => some ⟨61,11,2,0,23⟩
  | 63 => some ⟨3,11,1,0,23⟩
  | 69 => some ⟨3,11,1,0,23⟩
  | 71 => some ⟨71,23,7,0,11⟩
  | 81 => some ⟨3,11,1,0,23⟩
  | 93 => some ⟨3,11,1,0,23⟩
  | 109 => some ⟨109,23,18,0,11⟩
  | 119 => some ⟨17,11,8,0,23⟩
  | 129 => some ⟨3,11,1,0,23⟩
  | 141 => some ⟨3,11,1,0,23⟩
  | 147 => some ⟨3,11,1,0,23⟩
  | 153 => some ⟨3,11,1,0,23⟩
  | 161 => some ⟨23,11,11,0,23⟩
  | 171 => some ⟨3,11,1,0,23⟩
  | 207 => some ⟨3,11,1,0,23⟩
  | 217 => some ⟨31,23,5,0,11⟩
  | 223 => some ⟨223,11,111,0,23⟩
  | 237 => some ⟨3,11,1,0,23⟩
  | 279 => some ⟨3,11,1,0,23⟩
  | 327 => some ⟨3,11,1,0,23⟩
  | 329 => some ⟨47,11,23,0,23⟩
  | 373 => some ⟨373,23,62,0,11⟩
  | 399 => some ⟨3,11,1,0,23⟩
  | 459 => some ⟨3,11,1,0,23⟩
  | 483 => some ⟨3,11,1,0,23⟩
  | 589 => some ⟨31,23,5,0,11⟩
  | 613 => some ⟨613,23,102,0,11⟩
  | 681 => some ⟨3,11,1,0,23⟩
  | 711 => some ⟨3,11,1,0,23⟩
  | 789 => some ⟨3,11,1,0,23⟩
  | 987 => some ⟨3,11,1,0,23⟩
  | 1077 => some ⟨3,11,1,0,23⟩
  | 1207 => some ⟨71,23,7,0,11⟩
  | 1449 => some ⟨3,11,1,0,23⟩
  | 1561 => some ⟨223,11,111,0,23⟩
  | 1767 => some ⟨3,11,1,0,23⟩
  | 2133 => some ⟨3,11,1,0,23⟩
  | 2793 => some ⟨3,11,1,0,23⟩
  | 3541 => some ⟨3541,23,354,0,11⟩
  | 4377 => some ⟨3,11,1,0,23⟩
  | 5301 => some ⟨3,11,1,0,23⟩
  | _ => none

private def keep_11_23 : List (ℕ × ℤ) := [(43,12),(49,57),(49,244),(79,27),(79,588),(83,119),(83,372),(107,59),(107,708),(133,21),(133,1132),(227,3),(263,12),(263,2531),(359,3),(931,3),(931,9892),(1459,3),(1459,15612)]

private theorem grid_11_23 : divisorGrid 11 23 150 qInputs_11_23 keep_11_23 := by decide +kernel


private def types_frontier_mixed_539_497_244 : List RowType := [(18,34),(19,37),(20,36),(21,31),(22,22),(22,44),(23,31),(24,36),(25,37),(26,34),(27,27),(29,45),(30,48),(31,47),(32,42),(33,33),(34,42),(36,48)]
private def stage_0_frontier_mixed_539_497_244 : Stage := [
  ((18,34),⟨⟨3234000,0,(-38710),(-2070)⟩,[0,0,0,1241856,0,0,0,0,0,0,0],123⟩),
  ((19,37),⟨⟨0,0,(-195085000),0⟩,[0,0,0,0,0,0,0,933570000,0,2004764400,0],2692173⟩),
  ((20,36),⟨⟨0,0,(-7938),(-113)⟩,[0,202664,0,0,0,0,0,0,19404,175175,0],108⟩),
  ((21,31),⟨⟨543312,0,(-15435),(-147)⟩,[0,0,0,113190,0,0,0,0,0,0,0],85⟩),
  ((22,22),⟨⟨279202,0,0,(-550)⟩,[0,0,5390,32340,0,0,0,0,0,0,0],61⟩),
  ((22,44),⟨⟨284592,0,0,(-550)⟩,[0,0,0,26950,0,0,0,0,0,0,0],61⟩),
  ((23,31),⟨⟨164934,0,7399,(-569)⟩,[0,0,0,151998,0,0,0,0,0,0,0],33⟩),
  ((24,36),⟨⟨162162,0,0,(-242)⟩,[0,40964,0,0,0,0,0,0,0,0,44660],27⟩),
  ((25,37),⟨⟨23963121,0,0,(-35761)⟩,[0,6053362,0,0,0,0,0,0,0,0,6599530],3990⟩),
  ((26,34),⟨⟨1182411846,0,53043431,(-4079152)⟩,[0,0,0,1089673662,0,0,0,0,0,0,0],236577⟩),
  ((27,27),⟨⟨284592,0,0,(-550)⟩,[0,0,0,26950,0,0,0,0,0,0,0],61⟩),
  ((29,45),⟨⟨0,0,(-320882796),(-4567761)⟩,[0,8192415088,0,0,0,0,0,0,784380168,7081209850,0],4365790⟩),
  ((30,48),⟨⟨0,0,(-93834000),0⟩,[358340000,0,0,0,0,0,0,825740000,0,1332090000,0],937137⟩),
  ((31,47),⟨⟨(-587989710),55390335,(-3486105),(-1059270)⟩,[0,0,0,127823850,0,0,0,0,0,0,0],11858⟩),
  ((32,42),⟨⟨142032,0,(-4774),0⟩,[0,4356,7062,11836,0,0,0,0,0,17996,28776],15⟩),
  ((33,33),⟨⟨0,0,(-12250),195⟩,[114807,0,0,0,0,0,0,0,0,35035,163856],146⟩),
  ((34,42),⟨⟨0,0,(-550000),0⟩,[1950000,0,0,0,0,0,0,4950000,0,0,0],9353⟩)]
private theorem frontier_mixed_539_497_244 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=539) : ¬∃ f : G → ℤ, IsSDS 497 244 f :=
  abelian_short_mixed G 11 49 15 1 1 0 497 244 23 33 6 25 9 2
    types_frontier_mixed_539_497_244 [stage_0_frontier_mixed_539_497_244] ⟨⟨(-36),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_869_841_588 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=869) : ¬∃ f : G → ℤ, IsSDS 841 588 f :=
  abelian_short_linear G 11 79 15 1 1 0 841 588 23 65 6 25
    ⟨⟨75208,(-1976),(-161),15⟩,[494,0,0,0,0,0,0,0,0,104,0],0⟩ hG (by decide +kernel)




private def types_frontier_mixed_1177_961_708 : List RowType := [(68,72),(68,94),(69,85),(70,90),(71,87),(72,76),(72,98),(73,79),(73,101),(74,74),(74,96),(75,83),(75,105),(76,84),(76,106),(77,77),(77,99),(78,84),(78,106),(81,101),(85,85),(89,95)]
private def stage_0_frontier_mixed_1177_961_708 : Stage := [
  ((68,72),⟨⟨0,0,(-5335),0⟩,[0,0,0,0,210870,0,0,0,0,0,0],48⟩),
  ((68,94),⟨⟨0,(-75603),50325,0⟩,[0,0,0,0,0,0,0,0,419452,0,0],136⟩),
  ((69,85),⟨⟨0,(-4180),0,0⟩,[0,0,0,0,0,0,0,43186,101420,0,0],27⟩),
  ((70,90),⟨⟨5445230,0,0,(-1190)⟩,[0,12840,0,0,0,0,529008,0,314366,0,142310],167⟩),
  ((73,79),⟨⟨0,(-7700),0,0⟩,[0,0,0,0,0,0,0,0,70510,0,0],89⟩),
  ((73,101),⟨⟨152898,(-2142),0,0⟩,[0,30040,0,0,34,0,0,0,0,0,0],1⟩),
  ((74,96),⟨⟨112431,(-1617),0,0⟩,[0,0,0,0,0,1210,1683,0,0,0,0],1⟩),
  ((75,83),⟨⟨0,(-5808),0,0⟩,[52426,270270,0,0,0,0,0,0,0,0,0],37⟩),
  ((75,105),⟨⟨(-25557378),0,822295,(-6761)⟩,[736802,0,0,0,0,0,0,0,0,0,0],149⟩),
  ((76,106),⟨⟨81286,(-1292),0,0⟩,[14766,3936,0,0,1454,0,0,0,0,0,0],1⟩),
  ((77,77),⟨⟨0,0,0,(-968)⟩,[3441548,0,0,0,0,0,0,0,0,35310,3851144],507⟩),
  ((77,99),⟨⟨1092344,(-14960),0,0⟩,[660,0,0,0,0,0,0,0,0,0,0],13⟩),
  ((78,84),⟨⟨0,0,(-1067),0⟩,[1089,0,0,0,0,0,54076,0,0,0,0],9⟩),
  ((78,106),⟨⟨38470,(-702),0,0⟩,[3968,0,0,0,0,0,6464,0,0,0,0],1⟩),
  ((81,101),⟨⟨(-16830),0,0,0⟩,[0,0,0,4290,0,0,0,0,0,0,0],1⟩),
  ((85,85),⟨⟨0,0,0,(-1504001978)⟩,[0,0,0,0,0,0,0,0,0,0,0],423716023⟩),
  ((89,95),⟨⟨0,(-10670),0,0⟩,[0,0,0,0,0,0,0,93610,0,206976,0],89⟩)]
private theorem frontier_mixed_1177_961_708 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1177) : ¬∃ f : G → ℤ, IsSDS 961 708 f :=
  abelian_short_mixed G 11 107 15 1 1 0 961 708 23 83 6 25 39 4
    types_frontier_mixed_1177_961_708 [stage_0_frontier_mixed_1177_961_708] ⟨⟨76,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_1463_1385_1132 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1463) : ¬∃ f : G → ℤ, IsSDS 1385 1132 f :=
  abelian_short_linear G 11 133 15 1 1 0 1385 1132 23 117 6 25
    ⟨⟨0,109,0,(-1)⟩,[110,222,336,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_2893_265_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2893) : ¬∃ f : G → ℤ, IsSDS 265 12 f :=
  abelian_short_linear G 11 263 15 3 1 0 265 12 23 17 6 25
    ⟨⟨0,(-457),184,7⟩,[0,0,0,610,0,0,0,806,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2893_2784_2531 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2893) : ¬∃ f : G → ℤ, IsSDS 2784 2531 f :=
  abelian_short_linear G 11 263 15 1 1 0 2784 2531 23 246 6 25
    ⟨⟨238,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3949_256_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3949) : ¬∃ f : G → ℤ, IsSDS 256 3 f :=
  abelian_short_linear G 11 359 15 6 1 0 256 3 23 10 6 25
    ⟨⟨0,(-3333),644,95⟩,[0,0,0,0,220,0,1122,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10241_256_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10241) : ¬∃ f : G → ℤ, IsSDS 256 3 f :=
  abelian_short_linear G 11 931 15 3 1 0 256 3 23 16 6 25
    ⟨⟨0,0,68438576,(-28895348)⟩,[0,0,0,0,0,1237952179,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10241_10145_9892 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10241) : ¬∃ f : G → ℤ, IsSDS 10145 9892 f :=
  abelian_short_linear G 11 931 15 1 1 0 10145 9892 23 915 6 25
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_16049_256_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=16049) : ¬∃ f : G → ℤ, IsSDS 256 3 f :=
  abelian_short_linear G 11 1459 15 1 1 0 256 3 23 20 6 25
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_16049_15865_15612 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=16049) : ¬∃ f : G → ℤ, IsSDS 15865 15612 f :=
  abelian_short_linear G 11 1459 15 1 1 0 15865 15612 23 1439 6 25
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_11_23_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=11*m)
    (hm : 11 < m) (hn : k-l=(11:ℤ)*23) : False := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have row := endpoint_case (s:=23) hf hg hn (by decide) hm grid_11_23
  simp only [keep_11_23,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=265 := by omega
    rw [hk,hL] at hf
    exact Signed39.Template.no_473_265_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=310 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_539_310_57 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=497 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_539_497_244 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=280 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_869_280_27 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=841 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_869_841_588 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=372 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_913_372_119 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_913_625_372 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=312 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1177_312_59 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=961 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1177_961_708 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=274 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1463_274_21 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1385 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1463_1385_1132 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=256 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2497_256_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=265 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2893_265_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2784 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2893_2784_2531 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=256 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3949_256_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=256 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10241_256_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=10145 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10241_10145_9892 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=256 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_16049_256_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=15865 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_16049_15865_15612 G hg ⟨f,hf⟩

end Signed39.Contraction
