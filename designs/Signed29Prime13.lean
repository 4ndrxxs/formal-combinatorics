import Signed29Grid13Part0
import Signed29Grid13Part12
import Signed29Grid13Part24
import Signed29Grid13Part36
import Signed29Grid13Part48
import Signed29Fibre1391W441
import Signed29Fibre5707W378
import Signed29Fibre1807W1369
import Signed29Fibre2327W378
import Signed29Case1339W705
import Signed29Case1339W718
import Signed29Case2353W393
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_13_29 : divisorGrid 13 29 206 qInputs_13_29 keep_13_29 := by
  intro d
  fin_cases d
  · exact grid13x29Case0
  · exact grid13x29Case1
  · exact grid13x29Case2
  · exact grid13x29Case3
  · exact grid13x29Case4
  · exact grid13x29Case5
  · exact grid13x29Case6
  · exact grid13x29Case7
  · exact grid13x29Case8
  · exact grid13x29Case9
  · exact grid13x29Case10
  · exact grid13x29Case11
  · exact grid13x29Case12
  · exact grid13x29Case13
  · exact grid13x29Case14
  · exact grid13x29Case15
  · exact grid13x29Case16
  · exact grid13x29Case17
  · exact grid13x29Case18
  · exact grid13x29Case19
  · exact grid13x29Case20
  · exact grid13x29Case21
  · exact grid13x29Case22
  · exact grid13x29Case23
  · exact grid13x29Case24
  · exact grid13x29Case25
  · exact grid13x29Case26
  · exact grid13x29Case27
  · exact grid13x29Case28
  · exact grid13x29Case29
  · exact grid13x29Case30
  · exact grid13x29Case31
  · exact grid13x29Case32
  · exact grid13x29Case33
  · exact grid13x29Case34
  · exact grid13x29Case35
  · exact grid13x29Case36
  · exact grid13x29Case37
  · exact grid13x29Case38
  · exact grid13x29Case39
  · exact grid13x29Case40
  · exact grid13x29Case41
  · exact grid13x29Case42
  · exact grid13x29Case43
  · exact grid13x29Case44
  · exact grid13x29Case45
  · exact grid13x29Case46
  · exact grid13x29Case47
  · exact grid13x29Case48
  · exact grid13x29Case49
  · exact grid13x29Case50
  · exact grid13x29Case51
  · exact grid13x29Case52
  · exact grid13x29Case53
  · exact grid13x29Case54
  · exact grid13x29Case55
  · exact grid13x29Case56
  · exact grid13x29Case57





private def types_frontier_mixed_1391_1234_857 : List RowType := [(66,74),(66,100),(67,75),(67,101),(68,68),(68,94),(69,79),(69,105),(70,82),(71,77),(71,103),(72,90),(73,95),(76,88),(77,87),(78,78),(78,104),(81,81),(84,90),(85,103),(90,100)]
private def stage_0_frontier_mixed_1391_1234_857 : Stage := [
  ((66,74),⟨⟨120697070,0,0,(-21242)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,43602286],1449⟩),
  ((66,100),⟨⟨401417562,(-9663277),(-33384),58123⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],153⟩),
  ((67,75),⟨⟨(-14820),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,2210],1⟩),
  ((68,68),⟨⟨2512068,(-35750),0,0⟩,[0,0,0,0,0,0,0,10062,0,0,0,0,0],19⟩),
  ((70,82),⟨⟨215927712,(-5199558),0,31109⟩,[0,0,0,0,0,0,0,1033513,0,0,0,0,0],36⟩),
  ((71,77),⟨⟨751140,0,0,(-169)⟩,[216996,0,0,0,0,0,0,0,0,0,0,0,0],22⟩),
  ((71,103),⟨⟨673582,(-10088),0,0⟩,[88712,0,0,0,0,0,0,0,0,0,0,0,0],9⟩),
  ((72,90),⟨⟨37481886,0,0,(-8619)⟩,[10301746,0,0,0,0,0,0,0,7251283,0,0,0,0],869⟩),
  ((76,88),⟨⟨0,0,0,(-286)⟩,[0,1043250,0,0,0,0,0,0,186394,0,0,0,0],147⟩),
  ((78,78),⟨⟨0,0,0,(-221)⟩,[0,0,0,0,0,0,376961,0,0,0,0,0,0],270⟩),
  ((78,104),⟨⟨112580,(-1638),0,0⟩,[0,0,0,0,0,0,988,0,0,0,0,0,28210],1⟩),
  ((81,81),⟨⟨0,0,0,(-4117767)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],1033717⟩),
  ((84,90),⟨⟨(-13728),0,0,0⟩,[0,0,0,0,0,0,0,5850,0,0,0,0,0],1⟩),
  ((85,103),⟨⟨88010,(-1352),0,0⟩,[0,0,0,0,0,0,17680,0,0,0,0,0,0],1⟩),
  ((90,100),⟨⟨1167156,0,0,(-445)⟩,[585504,0,0,0,0,814912,0,0,0,0,0,0,0],144⟩)]
private theorem frontier_mixed_1391_1234_857 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1391) : ¬∃ f : G → ℤ, IsSDS 1234 857 f :=
  abelian_short_mixed G 13 107 18 1 1 0 1234 857 29 84 11 49 33 4
    types_frontier_mixed_1391_1234_857 [stage_0_frontier_mixed_1391_1234_857] ⟨⟨77,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1807_498_121 : List RowType := [(18,36),(19,43),(20,30),(21,49),(22,48),(23,27),(23,53),(24,38),(25,29),(25,55),(26,26),(26,52),(27,29),(27,55),(28,38),(29,53),(30,48),(31,49),(32,56),(33,43),(34,62),(35,61),(36,40),(36,66),(37,51),(38,42),(38,68),(39,39),(39,65),(40,42),(40,68),(41,51),(42,66),(43,61),(44,62),(45,69),(46,56),(47,49),(47,75),(48,48),(48,74),(49,53),(49,79),(50,64),(51,55),(51,81),(52,52),(52,78),(53,55),(53,81),(54,64)]
private def stage_0_frontier_mixed_1807_498_121 : Stage := [
  ((18,36),⟨⟨(-2291276),0,71724,(-724)⟩,[0,252980,0,0,0,0,0,0,0,112034,0,0,0],19⟩),
  ((24,38),⟨⟨(-1741948),0,76311,(-1121)⟩,[0,303576,0,0,0,0,0,0,0,39754,0,0,0],15⟩),
  ((26,26),⟨⟨0,0,0,(-403)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],27⟩),
  ((26,52),⟨⟨(-1756404),0,0,65⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],36⟩),
  ((27,29),⟨⟨(-8041150),0,141502,(-82)⟩,[0,0,0,0,0,0,0,0,0,0,1973244,0,0],263⟩),
  ((29,53),⟨⟨(-8659144),0,203635,(-3805)⟩,[0,3299582,238524,0,0,238524,0,0,0,0,0,2204540,0],241⟩),
  ((36,40),⟨⟨(-408954),0,6900,(-4)⟩,[0,0,54522,0,0,0,0,0,0,0,0,0,18460],7⟩),
  ((38,42),⟨⟨0,0,0,(-1651)⟩,[375856,0,0,0,0,0,0,0,0,0,0,0,0],192⟩),
  ((38,68),⟨⟨(-12338196),0,353060,(-2800)⟩,[0,430066,0,0,0,0,0,2056366,0,0,430066,0,0],93⟩),
  ((39,65),⟨⟨(-4488588),0,0,2067⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],64⟩),
  ((41,51),⟨⟨7686978,(-1304654),443688,13630⟩,[1398618,0,0,0,0,0,0,0,0,0,0,0,2511730],147⟩),
  ((44,62),⟨⟨6104046,(-659555),198492,5683⟩,[1647984,0,0,0,0,0,0,0,0,0,0,0,0],132⟩),
  ((45,69),⟨⟨(-7692816),0,358620,(-4386)⟩,[244362,0,0,0,0,0,0,0,0,0,0,0,0],19⟩),
  ((47,49),⟨⟨(-14535508),0,251451,(-821)⟩,[4994548,0,3220074,0,0,0,0,419224,0,0,0,0,0],276⟩),
  ((48,74),⟨⟨(-6335342),0,242138,(-2470)⟩,[361400,0,0,0,0,0,0,0,0,0,0,0,0],33⟩),
  ((49,79),⟨⟨(-6645868),0,311360,(-3922)⟩,[209334,0,0,0,0,0,0,0,0,0,0,0,0],19⟩),
  ((51,81),⟨⟨71127134,(-4631341),683741,45976⟩,[5619770,0,0,0,0,0,0,0,0,0,0,0,0],320⟩),
  ((52,78),⟨⟨(-2473783),0,123988,(-4389)⟩,[0,0,0,0,0,0,0,0,0,0,1808807,0,196963],160⟩),
  ((53,81),⟨⟨(-4396431),0,210724,(-3245)⟩,[0,247559,0,0,0,0,0,0,0,0,0,0,0],36⟩),
  ((54,64),⟨⟨(-13772954),0,179727,1073⟩,[0,0,0,0,480662,0,0,0,0,0,3187548,975780,0],308⟩)]
private theorem frontier_mixed_1807_498_121 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1807) : ¬∃ f : G → ℤ, IsSDS 498 121 f :=
  abelian_short_mixed G 13 139 18 1 1 0 498 121 29 36 11 49 107 10
    types_frontier_mixed_1807_498_121 [stage_0_frontier_mixed_1807_498_121] ⟨⟨49920,(-3809),420,53⟩,[1638,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_42887_378_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=42887) : ¬∃ f : G → ℤ, IsSDS 378 1 f :=
  abelian_short_linear G 13 3299 18 6 1 0 378 1 29 16 11 49
    ⟨⟨0,(-21593),2958,115⟩,[0,0,0,0,0,1560,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_42887_42849_42472 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=42887) : ¬∃ f : G → ℤ, IsSDS 42849 42472 f :=
  abelian_short_linear G 13 3299 18 1 1 0 42849 42472 29 3283 11 49
    ⟨⟨(-3299),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_67223_378_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=67223) : ¬∃ f : G → ℤ, IsSDS 378 1 f :=
  abelian_short_linear G 13 5171 18 4 1 0 378 1 29 20 11 49
    ⟨⟨0,0,225,(-133)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_67223_67081_66704 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=67223) : ¬∃ f : G → ℤ, IsSDS 67081 66704 f :=
  abelian_short_linear G 13 5171 18 1 1 0 67081 66704 29 5151 11 49
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_81419_378_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=81419) : ¬∃ f : G → ℤ, IsSDS 378 1 f :=
  abelian_short_linear G 13 6263 18 3 1 0 378 1 29 22 11 49
    ⟨⟨0,0,5175943,(-8095000)⟩,[0,0,0,0,0,0,0,0,15985000,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_81419_81225_80848 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=81419) : ¬∃ f : G → ℤ, IsSDS 81225 80848 f :=
  abelian_short_linear G 13 6263 18 1 1 0 81225 80848 29 6241 11 49
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_96967_378_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=96967) : ¬∃ f : G → ℤ, IsSDS 378 1 f :=
  abelian_short_linear G 13 7459 18 2 1 0 378 1 29 24 11 49
    ⟨⟨6,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_96967_96721_96344 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=96967) : ¬∃ f : G → ℤ, IsSDS 96721 96344 f :=
  abelian_short_linear G 13 7459 18 1 1 0 96721 96344 29 7435 11 49
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_132119_378_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=132119) : ¬∃ f : G → ℤ, IsSDS 378 1 f :=
  abelian_short_linear G 13 10163 18 0 1 0 378 1 29 28 11 49
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_132119_131769_131392 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=132119) : ¬∃ f : G → ℤ, IsSDS 131769 131392 f :=
  abelian_short_linear G 13 10163 18 0 1 0 131769 131392 29 10135 11 49
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_13_29_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=13*m)
    (hm : 13 < m) (hn : k-l=(13:ℤ)*29) : False := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have row := endpoint_case (s:=29) hf hg hn (by decide) hm grid_13_29
  simp only [keep_13_29,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=705 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1339_705_328 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=718 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1339_718_341 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=441 := by omega
    rw [hk,hL] at hf
    exact fibre_1391_441 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1234 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1391_1234_857 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=498 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1807_498_121 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1369 := by omega
    rw [hk,hL] at hf
    exact fibre_1807_1369 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=378 := by omega
    rw [hk,hL] at hf
    exact fibre_2327_378 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=393 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2353_393_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=378 := by omega
    rw [hk,hL] at hf
    exact fibre_5707_378 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=378 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_42887_378_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=42849 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_42887_42849_42472 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=378 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_67223_378_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=67081 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_67223_67081_66704 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=378 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_81419_378_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=81225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_81419_81225_80848 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=378 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_96967_378_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=96721 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_96967_96721_96344 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=378 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_132119_378_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=131769 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_132119_131769_131392 G hg ⟨f,hf⟩

end Signed39.Contraction
