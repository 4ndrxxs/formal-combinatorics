import Signed29Grid7Part0
import Signed29Grid7Part12
import Signed29Grid7Part24
import Signed29Grid7Part36
import Signed29Grid7Part48
import Signed29Fibre973W225
import Signed29Fibre2933W204
import Signed29Fibre721W256
import Signed29Fibre581W204
import Signed29Fibre1169W225
import Signed29Fibre1561W204
import Signed29Fibre413W324
import Signed29Fibre721W585
import Signed29Fibre413W289
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_7_29 : divisorGrid 7 29 151 qInputs_7_29 keep_7_29 := by
  intro d
  fin_cases d
  · exact grid7x29Case0
  · exact grid7x29Case1
  · exact grid7x29Case2
  · exact grid7x29Case3
  · exact grid7x29Case4
  · exact grid7x29Case5
  · exact grid7x29Case6
  · exact grid7x29Case7
  · exact grid7x29Case8
  · exact grid7x29Case9
  · exact grid7x29Case10
  · exact grid7x29Case11
  · exact grid7x29Case12
  · exact grid7x29Case13
  · exact grid7x29Case14
  · exact grid7x29Case15
  · exact grid7x29Case16
  · exact grid7x29Case17
  · exact grid7x29Case18
  · exact grid7x29Case19
  · exact grid7x29Case20
  · exact grid7x29Case21
  · exact grid7x29Case22
  · exact grid7x29Case23
  · exact grid7x29Case24
  · exact grid7x29Case25
  · exact grid7x29Case26
  · exact grid7x29Case27
  · exact grid7x29Case28
  · exact grid7x29Case29
  · exact grid7x29Case30
  · exact grid7x29Case31
  · exact grid7x29Case32
  · exact grid7x29Case33
  · exact grid7x29Case34
  · exact grid7x29Case35
  · exact grid7x29Case36
  · exact grid7x29Case37
  · exact grid7x29Case38
  · exact grid7x29Case39
  · exact grid7x29Case40
  · exact grid7x29Case41
  · exact grid7x29Case42
  · exact grid7x29Case43
  · exact grid7x29Case44
  · exact grid7x29Case45
  · exact grid7x29Case46
  · exact grid7x29Case47
  · exact grid7x29Case48
  · exact grid7x29Case49
  · exact grid7x29Case50
  · exact grid7x29Case51
  · exact grid7x29Case52
  · exact grid7x29Case53
  · exact grid7x29Case54
  · exact grid7x29Case55
  · exact grid7x29Case56
  · exact grid7x29Case57



private theorem frontier_mixed_203_202_neg1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=203) : ¬∃ f : G → ℤ, IsSDS 202 (-1) f :=
  abelian_short_linear G 7 29 13 3 1 0 202 (-1) 29 0 4 33
    ⟨⟨0,(-1),0,(-1)⟩,[0,2,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_973_904_701 : List RowType := [(105,105),(105,119),(105,133),(106,118),(106,132),(107,115),(107,129),(108,110),(108,124),(108,138),(109,117),(109,131),(111,111),(111,125),(111,139),(113,125),(116,124),(116,138),(118,118),(118,132),(125,125)]
private def stage_0_frontier_mixed_973_904_701 : Stage := [
  ((105,133),⟨⟨126034636,0,(-291066),(-8266)⟩,[0,0,0,0,0,0,14124068],751⟩),
  ((106,118),⟨⟨348473,0,0,(-33)⟩,[0,0,0,0,6255,0,32248],4⟩),
  ((106,132),⟨⟨14690,(-243),0,1⟩,[0,0,0,0,42,0,60],0⟩),
  ((107,115),⟨⟨4331240,0,0,(-424)⟩,[0,0,0,0,651354,0,311360],59⟩),
  ((107,129),⟨⟨14732,(-243),0,1⟩,[0,0,0,0,0,0,18],0⟩),
  ((108,110),⟨⟨12457041,0,0,(-1457)⟩,[0,5255312,0,0,0,0,2421936],236⟩),
  ((108,138),⟨⟨14690,(-243),0,1⟩,[0,0,0,0,42,0,60],0⟩),
  ((109,131),⟨⟨5242107,0,0,(-615)⟩,[0,0,0,0,0,0,452028],118⟩),
  ((111,111),⟨⟨1988812,0,0,(-196)⟩,[77840,0,0,0,0,0,0],33⟩),
  ((111,125),⟨⟨26843124,0,0,(-2492)⟩,[0,0,0,0,0,0,4903920],221⟩),
  ((111,139),⟨⟨15278046,0,0,(-1414)⟩,[0,0,0,0,449526,0,3269280],109⟩),
  ((116,124),⟨⟨9546089560,0,0,(-822352)⟩,[0,338471700,0,0,0,0,0],110313⟩),
  ((118,118),⟨⟨0,0,(-217),0⟩,[2443,924,0,0,0,0,0],1⟩),
  ((118,132),⟨⟨0,0,(-217),0⟩,[2443,924,0,0,0,0,0],1⟩),
  ((125,125),⟨⟨0,0,(-165639915),0⟩,[0,0,0,0,0,0,0],951691⟩)]
private theorem frontier_mixed_973_904_701 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=973) : ¬∃ f : G → ℤ, IsSDS 904 701 f :=
  abelian_short_mixed G 7 139 13 2 1 0 904 701 29 118 4 33 20 1
    types_frontier_mixed_973_904_701 [stage_0_frontier_mixed_973_904_701] ⟨⟨116,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1169_1072_869 : List RowType := [(131,143),(131,157),(132,132),(132,146),(132,160),(133,133),(133,147),(133,161),(134,146),(134,160),(135,143),(135,157),(136,138),(136,152),(136,166),(137,145),(137,159),(139,139),(139,153),(139,167),(141,153),(144,152),(146,146),(146,160),(153,153)]
private def stage_0_frontier_mixed_1169_1072_869 : Stage := [
  ((131,143),⟨⟨22278,(-299),0,1⟩,[0,0,0,0,42,0,60],0⟩),
  ((131,157),⟨⟨22278,(-299),0,1⟩,[0,0,0,0,42,0,60],0⟩),
  ((132,160),⟨⟨3904460,(-52605),0,175⟩,[0,0,0,0,0,0,0],1⟩),
  ((133,133),⟨⟨6174992,0,0,(-416)⟩,[0,1648624,0,0,0,0,877084],57⟩),
  ((133,147),⟨⟨18463520,(-248830),0,822⟩,[0,224448,0,0,0,0,35404],7⟩),
  ((134,146),⟨⟨98081772,(-1324644),0,4434⟩,[0,0,0,0,485302,0,0],17⟩),
  ((135,143),⟨⟨518368,0,0,(-32)⟩,[0,0,0,0,48430,0,0],5⟩),
  ((135,157),⟨⟨45623064,(-619904),0,2080⟩,[0,0,0,0,203406,0,116232],9⟩),
  ((136,138),⟨⟨4659300,0,0,(-310)⟩,[0,710752,0,4342,0,0,0],57⟩),
  ((136,152),⟨⟨263857662,(-3477775),0,11237⟩,[0,0,0,0,0,0,0],114⟩),
  ((136,166),⟨⟨248575158,(-3350855),0,11233⟩,[0,0,0,0,0,0,195390],21⟩),
  ((137,145),⟨⟨12235923,0,0,(-707)⟩,[0,196392,0,0,0,0,0],96⟩),
  ((139,153),⟨⟨0,0,(-4216),0⟩,[0,0,0,0,0,128680,65980],23⟩),
  ((153,153),⟨⟨0,0,0,(-605497430)⟩,[0,0,0,0,0,0,0],520264623⟩)]
private theorem frontier_mixed_1169_1072_869 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1169) : ¬∃ f : G → ℤ, IsSDS 1072 869 f :=
  abelian_short_mixed G 7 167 13 2 1 0 1072 869 29 144 4 33 24 1
    types_frontier_mixed_1169_1072_869 [stage_0_frontier_mixed_1169_1072_869] ⟨⟨(-18753),274,0,(-1)⟩,[0,0,0,0,33,0,65],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15673_204_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15673) : ¬∃ f : G → ℤ, IsSDS 204 1 f :=
  abelian_short_linear G 7 2239 13 5 1 0 204 1 29 18 4 33
    ⟨⟨(-5355124164),0,170969940,0⟩,[0,357172387,0,0,0,372768318,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15673_15625_15422 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15673) : ¬∃ f : G → ℤ, IsSDS 15625 15422 f :=
  abelian_short_linear G 7 2239 13 2 1 0 15625 15422 29 2221 4 33
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23513_204_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23513) : ¬∃ f : G → ℤ, IsSDS 204 1 f :=
  abelian_short_linear G 7 3359 13 3 1 0 204 1 29 22 4 33
    ⟨⟨11,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23513_23409_23206 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23513) : ¬∃ f : G → ℤ, IsSDS 23409 23206 f :=
  abelian_short_linear G 7 3359 13 2 1 0 23409 23206 29 3337 4 33
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28021_204_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28021) : ¬∃ f : G → ℤ, IsSDS 204 1 f :=
  abelian_short_linear G 7 4003 13 2 1 0 204 1 29 24 4 33
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28021_27889_27686 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28021) : ¬∃ f : G → ℤ, IsSDS 27889 27686 f :=
  abelian_short_linear G 7 4003 13 2 1 0 27889 27686 29 3979 4 33
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_32921_204_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=32921) : ¬∃ f : G → ℤ, IsSDS 204 1 f :=
  abelian_short_linear G 7 4703 13 1 1 0 204 1 29 26 4 33
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_32921_32761_32558 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=32921) : ¬∃ f : G → ℤ, IsSDS 32761 32558 f :=
  abelian_short_linear G 7 4703 13 1 1 0 32761 32558 29 4677 4 33
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_7_29_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=7*m)
    (hm : 7 < m) (hn : k-l=(7:ℤ)*29) : False := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have row := endpoint_case (s:=29) hf hg hn (by decide) hm grid_7_29
  simp only [keep_7_29,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=202 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_203_202_neg1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=289 := by omega
    rw [hk,hL] at hf
    exact fibre_413_289 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=324 := by omega
    rw [hk,hL] at hf
    exact fibre_413_324 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=204 := by omega
    rw [hk,hL] at hf
    exact fibre_581_204 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=256 := by omega
    rw [hk,hL] at hf
    exact fibre_721_256 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=585 := by omega
    rw [hk,hL] at hf
    exact fibre_721_585 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=225 := by omega
    rw [hk,hL] at hf
    exact fibre_973_225 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=904 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_973_904_701 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=225 := by omega
    rw [hk,hL] at hf
    exact fibre_1169_225 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1072 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1169_1072_869 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=204 := by omega
    rw [hk,hL] at hf
    exact fibre_1561_204 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=204 := by omega
    rw [hk,hL] at hf
    exact fibre_2933_204 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=204 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15673_204_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=15625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15673_15625_15422 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=204 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23513_204_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=23409 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23513_23409_23206 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=204 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28021_204_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=27889 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28021_27889_27686 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=204 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_32921_204_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=32761 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_32921_32761_32558 G hg ⟨f,hf⟩

end Signed39.Contraction
