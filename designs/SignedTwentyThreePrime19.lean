import SignedTwentyThreeGrid19
import SignedTwentyThreeCase1957W484
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0



private theorem frontier_mixed_1273_600_163 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1273) : ¬∃ f : G → ℤ, IsSDS 600 163 f :=
  abelian_short_linear G 19 67 20 1 1 0 600 163 23 24 12 29
    ⟨⟨0,(-13471),3312,311⟩,[0,12540,0,0,0,0,0,0,27702,0,0,1254,0,0,0,0,0,0,9234],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1273_961_524 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1273) : ¬∃ f : G → ℤ, IsSDS 961 524 f :=
  abelian_short_linear G 19 67 20 1 1 0 961 524 23 43 12 29
    ⟨⟨0,0,383459388,(-14873729)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,2193847938,0,0,4033231362,1638200862,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1501_784_347 : List RowType := [(18,32),(18,70),(19,57),(20,32),(20,70),(21,33),(21,71),(22,60),(23,37),(23,75),(24,40),(24,78),(25,69),(26,48),(27,53),(28,46),(29,65),(30,34),(30,72),(31,67),(32,50),(33,59),(34,56),(35,41),(36,52),(37,51),(38,38),(38,76),(39,51),(40,52),(41,41),(42,56),(43,59),(44,50),(46,72),(47,65),(51,69),(55,71)]
private def stage_0_frontier_mixed_1501_784_347 : Stage := [
  ((19,57),⟨⟨(-20862),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((20,32),⟨⟨0,0,0,(-10792)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],3025⟩),
  ((26,48),⟨⟨(-370747),0,26860,(-625)⟩,[0,0,0,0,0,0,202635,0,0,0,0,0,0,0,0,0,0,0,0],12⟩),
  ((28,46),⟨⟨(-183122),0,6320,(-118)⟩,[0,0,0,0,0,21014,30020,0,0,0,0,0,0,0,0,0,3002,0,0],5⟩),
  ((30,34),⟨⟨0,0,0,(-15276)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],3025⟩),
  ((32,50),⟨⟨(-354236),0,9638,(-122)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],9⟩),
  ((33,59),⟨⟨(-93784),0,5029,(-169)⟩,[0,0,0,24966,0,58254,0,0,0,0,0,0,0,0,0,0,0,0,0],9⟩),
  ((36,52),⟨⟨(-657438),0,16827,(-213)⟩,[0,0,0,0,48032,0,0,0,0,0,0,0,0,0,0,0,0,0,0],34⟩),
  ((37,51),⟨⟨(-417278),0,11534,(-146)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],27⟩),
  ((38,76),⟨⟨(-51072),0,525,15⟩,[5130,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((39,51),⟨⟨(-294575279),0,0,153576⟩,[36397275,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],24572⟩),
  ((40,52),⟨⟨(-47953),0,0,25⟩,[5925,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((42,56),⟨⟨(-417278),0,11534,(-146)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],27⟩),
  ((43,59),⟨⟨(-657438),0,16827,(-213)⟩,[0,0,0,0,48032,0,0,0,0,0,0,0,0,0,0,0,0,0,0],34⟩),
  ((44,50),⟨⟨0,0,0,(-1444)⟩,[0,0,114076,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],507⟩),
  ((46,72),⟨⟨(-93784),0,5029,(-169)⟩,[0,0,0,24966,0,58254,0,0,0,0,0,0,0,0,0,0,0,0,0],9⟩),
  ((47,65),⟨⟨(-354236),0,9638,(-122)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],9⟩),
  ((51,69),⟨⟨(-342228),0,10665,(-173)⟩,[0,0,0,0,0,21014,39026,0,0,0,0,0,0,0,0,0,12008,0,0],8⟩)]
private def stage_1_frontier_mixed_1501_784_347 : Stage := [
  ((29,65),⟨⟨(-6656935),0,0,(-7049)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11153931,0,0,0],1248⟩),
  ((31,67),⟨⟨0,0,0,(-20026)⟩,[0,0,6340224,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11392590,0],1681⟩),
  ((35,41),⟨⟨0,0,0,(-771881383)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],135045760⟩),
  ((38,38),⟨⟨0,0,0,(-28272)⟩,[27720468,0,0,34420932,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],3025⟩),
  ((41,41),⟨⟨0,0,0,(-28272)⟩,[27720468,0,0,34420932,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],3025⟩),
  ((55,71),⟨⟨0,0,0,(-2166)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],275⟩)]
private theorem frontier_mixed_1501_784_347 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1501) : ¬∃ f : G → ℤ, IsSDS 784 347 f :=
  abelian_short_mixed G 19 79 20 1 1 0 784 347 23 38 12 29 25 6
    types_frontier_mixed_1501_784_347 [stage_0_frontier_mixed_1501_784_347,stage_1_frontier_mixed_1501_784_347] ⟨⟨0,0,25,(-2)⟩,[0,0,57,0,133,152,0,0,133,0,0,0,0,0,0,912,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1501_841_404 : List RowType := [(21,33),(21,71),(22,60),(23,37),(23,75),(24,40),(24,78),(25,69),(26,48),(27,53),(28,46),(29,65),(30,34),(30,72),(31,67),(32,50),(33,59),(34,56),(35,41),(36,52),(37,51),(38,38),(38,76),(39,51),(40,52),(41,41),(42,56),(43,59),(44,50),(46,72),(47,65),(51,69),(55,71)]
private def stage_0_frontier_mixed_1501_841_404 : Stage := [
  ((21,71),⟨⟨0,0,33417,(-2703)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,2710806,0,0,0,0,0],242⟩),
  ((23,75),⟨⟨(-43814),0,1534,(-30)⟩,[0,0,0,2508,0,5852,2774,0,0,798,0,0,0,0,0,0,0,0,0],1⟩),
  ((26,48),⟨⟨0,0,11060,(-406)⟩,[0,0,0,0,0,0,189126,0,0,0,0,0,0,0,0,0,0,0,0],15⟩),
  ((27,53),⟨⟨(-583889),0,6004,(-171)⟩,[0,0,0,25517,0,0,67545,0,97565,0,0,0,0,0,0,0,0,0,0],96⟩),
  ((30,72),⟨⟨(-15276),0,0,0⟩,[0,0,0,1064,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((32,50),⟨⟨(-1780186),0,37525,(-361)⟩,[0,78052,69046,0,123082,279186,0,0,0,0,0,0,0,0,0,0,0,0,0],48⟩),
  ((36,52),⟨⟨(-657438),0,16827,(-213)⟩,[0,0,0,0,48032,0,0,0,0,0,0,0,0,0,0,0,0,0,0],34⟩),
  ((37,51),⟨⟨(-417278),0,11534,(-146)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],27⟩),
  ((38,38),⟨⟨0,0,48269,(-1675)⟩,[333222,0,84056,585390,0,0,135090,0,0,0,0,0,0,0,0,0,0,0,0],58⟩),
  ((38,76),⟨⟨0,0,214248,(-7215)⟩,[1098732,0,0,2165943,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],272⟩),
  ((39,51),⟨⟨564376,0,0,(-475)⟩,[0,0,0,112575,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],82⟩),
  ((40,52),⟨⟨2108890000,0,0,(-1775000)⟩,[0,0,0,420656250,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],318577⟩),
  ((41,41),⟨⟨0,0,48269,(-1675)⟩,[333222,0,84056,585390,0,0,135090,0,0,0,0,0,0,0,0,0,0,0,0],58⟩),
  ((42,56),⟨⟨(-417278),0,11534,(-146)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],27⟩),
  ((43,59),⟨⟨(-657438),0,16827,(-213)⟩,[0,0,0,0,48032,0,0,0,0,0,0,0,0,0,0,0,0,0,0],34⟩),
  ((47,65),⟨⟨(-1780186),0,37525,(-361)⟩,[0,78052,69046,0,123082,279186,0,0,0,0,0,0,0,0,0,0,0,0,0],48⟩)]
private theorem frontier_mixed_1501_841_404 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1501) : ¬∃ f : G → ℤ, IsSDS 841 404 f :=
  abelian_short_mixed G 19 79 20 1 1 0 841 404 23 41 12 29 25 6
    types_frontier_mixed_1501_841_404 [stage_0_frontier_mixed_1501_841_404] ⟨⟨(-38950),0,2125,(-37)⟩,[0,0,0,0,0,0,4332,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_1957_1833_1396 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1957) : ¬∃ f : G → ℤ, IsSDS 1833 1396 f :=
  abelian_short_linear G 19 103 20 0 1 0 1833 1396 23 87 12 29
    ⟨⟨824,7,(-15),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2033_576_139 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2033) : ¬∃ f : G → ℤ, IsSDS 576 139 f :=
  abelian_short_linear G 19 107 20 1 1 0 576 139 23 28 12 29
    ⟨⟨0,(-454),259,3⟩,[3078,0,0,0,308,0,0,0,488,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2033_1545_1108 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2033) : ¬∃ f : G → ℤ, IsSDS 1545 1108 f :=
  abelian_short_linear G 19 107 20 1 1 0 1545 1108 23 79 12 29
    ⟨⟨0,0,6241,(-91)⟩,[0,0,0,0,0,0,266,0,0,0,0,0,2622,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4313_441_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4313) : ¬∃ f : G → ℤ, IsSDS 441 4 f :=
  abelian_short_linear G 19 227 20 6 1 0 441 4 23 7 12 29
    ⟨⟨0,(-88312),13944,2907⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7201_441_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7201) : ¬∃ f : G → ℤ, IsSDS 441 4 f :=
  abelian_short_linear G 19 379 20 7 1 0 441 4 23 9 12 29
    ⟨⟨0,(-9158),1173,223⟩,[0,0,0,0,0,0,0,0,342,0,0,0,0,0,2394,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20197_441_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20197) : ¬∃ f : G → ℤ, IsSDS 441 4 f :=
  abelian_short_linear G 19 1063 20 4 1 0 441 4 23 15 12 29
    ⟨⟨0,0,15394,(-8077)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20197_20068_19631 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20197) : ¬∃ f : G → ℤ, IsSDS 20068 19631 f :=
  abelian_short_linear G 19 1063 20 0 1 0 20068 19631 23 1048 12 29
    ⟨⟨(-1063),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_25973_441_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=25973) : ¬∃ f : G → ℤ, IsSDS 441 4 f :=
  abelian_short_linear G 19 1367 20 3 1 0 441 4 23 17 12 29
    ⟨⟨0,0,25,(-32)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_25973_25768_25331 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=25973) : ¬∃ f : G → ℤ, IsSDS 25768 25331 f :=
  abelian_short_linear G 19 1367 20 0 1 0 25768 25331 23 1350 12 29
    ⟨⟨(-1367),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_19_23_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=19*m)
    (hm : 19 < m) (hn : k-l=(19:ℤ)*23) : False := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  have row := endpoint_case (s:=23) hf hg hn (by decide) hm grid_19_23
  simp only [keep_19_23,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=600 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1273_600_163 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=961 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1273_961_524 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=784 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1501_784_347 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=841 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1501_841_404 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=484 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1957_484_47 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1833 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1957_1833_1396 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=576 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2033_576_139 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1545 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2033_1545_1108 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4313_441_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7201_441_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20197_441_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=20068 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20197_20068_19631 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_25973_441_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=25768 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_25973_25768_25331 G hg ⟨f,hf⟩

end Signed39.Contraction
