import Signed27Grid13Part0
import Signed27Grid13Part12
import Signed27Grid13Part24
import Signed27Grid13Part36
import Signed27Grid13Part48
import SignedLongLocalCases
import Signed27Case897W393
import Signed27Case1391W446
import Signed27Case2327W386
import Signed27Case2691W365
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_13_27 : divisorGrid 13 27 192 qInputs_13_27 keep_13_27 := by
  intro d
  fin_cases d
  · exact grid13x27Case0
  · exact grid13x27Case1
  · exact grid13x27Case2
  · exact grid13x27Case3
  · exact grid13x27Case4
  · exact grid13x27Case5
  · exact grid13x27Case6
  · exact grid13x27Case7
  · exact grid13x27Case8
  · exact grid13x27Case9
  · exact grid13x27Case10
  · exact grid13x27Case11
  · exact grid13x27Case12
  · exact grid13x27Case13
  · exact grid13x27Case14
  · exact grid13x27Case15
  · exact grid13x27Case16
  · exact grid13x27Case17
  · exact grid13x27Case18
  · exact grid13x27Case19
  · exact grid13x27Case20
  · exact grid13x27Case21
  · exact grid13x27Case22
  · exact grid13x27Case23
  · exact grid13x27Case24
  · exact grid13x27Case25
  · exact grid13x27Case26
  · exact grid13x27Case27
  · exact grid13x27Case28
  · exact grid13x27Case29
  · exact grid13x27Case30
  · exact grid13x27Case31
  · exact grid13x27Case32
  · exact grid13x27Case33
  · exact grid13x27Case34
  · exact grid13x27Case35
  · exact grid13x27Case36
  · exact grid13x27Case37
  · exact grid13x27Case38
  · exact grid13x27Case39
  · exact grid13x27Case40
  · exact grid13x27Case41
  · exact grid13x27Case42
  · exact grid13x27Case43
  · exact grid13x27Case44
  · exact grid13x27Case45
  · exact grid13x27Case46
  · exact grid13x27Case47
  · exact grid13x27Case48
  · exact grid13x27Case49
  · exact grid13x27Case50
  · exact grid13x27Case51
  · exact grid13x27Case52
  · exact grid13x27Case53



private theorem frontier_mixed_351_350_neg1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=351) : ¬∃ f : G → ℤ, IsSDS 350 (-1) f :=
  abelian_short_linear G 13 27 18 1 1 0 350 (-1) 27 0 7 29
    ⟨⟨26,0,(-1),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)



private def types_frontier_mixed_1391_1109_758 : List RowType := [(61,79),(61,105),(62,68),(62,94),(63,75),(63,101),(64,74),(64,100),(65,65),(65,91),(66,74),(66,100),(67,75),(67,101),(68,68),(68,94),(69,79),(69,105),(70,82),(71,77),(71,103),(72,90),(73,95),(76,88),(77,87),(78,78),(78,104),(81,81),(84,90),(85,103),(90,100)]
private def stage_0_frontier_mixed_1391_1109_758 : Stage := [
  ((62,68),⟨⟨0,0,0,(-91)⟩,[0,175266,0,0,0,0,0,0,0,0,0,0,0],81⟩),
  ((62,94),⟨⟨(-38633634),0,1019175,(-8901)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,2189434],728⟩),
  ((63,75),⟨⟨47619,(-975),0,0⟩,[0,0,0,0,0,0,4641,9321,0,0,0,0,0],2⟩),
  ((64,74),⟨⟨105716,0,0,(-26)⟩,[0,0,0,0,0,0,69550,0,0,0,0,0,0],3⟩),
  ((64,100),⟨⟨72676968,(-2026687),58422,13065⟩,[0,0,0,0,0,0,0,0,0,0,0,94588,0],44⟩),
  ((65,65),⟨⟨(-575874),0,17869,(-193)⟩,[58422,0,0,0,0,0,0,0,0,0,0,0,0],32⟩),
  ((65,91),⟨⟨96677282,(-2644291),0,17693⟩,[111280,52858,0,0,0,0,0,0,0,0,0,0,0],63⟩),
  ((66,74),⟨⟨(-1805518),0,55747,(-547)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,431210],43⟩),
  ((66,100),⟨⟨2845674,(-247988),180284,0⟩,[419952,0,0,0,0,0,0,0,0,0,0,0,914602],99⟩),
  ((67,75),⟨⟨(-15886),0,0,0⟩,[0,0,0,0,0,0,1066,0,0,0,0,0,3276],1⟩),
  ((69,79),⟨⟨0,(-2275),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,11674],17⟩),
  ((69,105),⟨⟨38330,(-722),0,0⟩,[1060,0,0,1666,0,0,322,2214,0,0,0,0,0],1⟩),
  ((71,77),⟨⟨751140,0,0,(-169)⟩,[216996,0,0,0,0,0,0,0,0,0,0,0,0],22⟩),
  ((71,103),⟨⟨4593510,(-118877),12519,568⟩,[222132,0,0,0,0,0,0,0,0,0,0,0,0],9⟩),
  ((76,88),⟨⟨0,0,0,(-286)⟩,[0,1043250,0,0,0,0,0,0,186394,0,0,0,0],147⟩),
  ((77,87),⟨⟨0,(-1157),0,0⟩,[0,0,27079,0,0,0,36283,0,0,0,0,17979,0],4⟩),
  ((78,78),⟨⟨0,0,0,(-221)⟩,[0,0,0,0,0,0,376961,0,0,0,0,0,0],270⟩),
  ((78,104),⟨⟨(-6092580),0,160179,(-1263)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],46⟩),
  ((81,81),⟨⟨0,0,0,(-448647384)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],112627655⟩),
  ((84,90),⟨⟨0,0,0,(-7878)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,12544038],7225⟩),
  ((90,100),⟨⟨1167156,0,0,(-445)⟩,[585504,0,0,0,0,814912,0,0,0,0,0,0,0],144⟩)]
private theorem frontier_mixed_1391_1109_758 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1391) : ¬∃ f : G → ℤ, IsSDS 1109 758 f :=
  abelian_short_mixed G 13 107 18 1 1 0 1109 758 27 79 7 29 33 4
    types_frontier_mixed_1391_1109_758 [stage_0_frontier_mixed_1391_1109_758] ⟨⟨0,0,2450,(-41)⟩,[0,0,0,22984,0,0,0,43875,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_2327_2141_1790 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2327) : ¬∃ f : G → ℤ, IsSDS 2141 1790 f :=
  abelian_short_linear G 13 179 18 1 1 0 2141 1790 27 157 7 29
    ⟨⟨93483,0,154,(-5)⟩,[0,0,0,0,8645,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_2691_2666_2315 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2691) : ¬∃ f : G → ℤ, IsSDS 2666 2315 f :=
  abelian_short_linear G 13 207 18 1 1 0 2666 2315 27 192 7 29
    ⟨⟨38502,(-393),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_13_27_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=13*m)
    (hm : 13 < m) (hn : k-l=(13:ℤ)*27) : False := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have row := endpoint_case (s:=27) hf hg hn (by decide) hm grid_13_27
  simp only [keep_13_27,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=350 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_351_350_neg1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=393 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_897_393_42 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=446 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1391_446_95 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1109 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1391_1109_758 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=386 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2327_386_35 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2141 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2327_2141_1790 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=352 := by omega
    rw [hk,hL] at hf
    exact local_2353_352 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=365 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2691_365_14 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2666 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2691_2666_2315 G hg ⟨f,hf⟩

end Signed39.Contraction
