import Signed25Grid13Part0
import Signed25Grid13Part12
import Signed25Grid13Part24
import Signed25Grid13Part36
import Signed25Grid13Part48
import Signed25Case2379W326
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_13_25 : divisorGrid 13 25 177 qInputs_13_25 keep_13_25 := by
  intro d
  fin_cases d
  · exact grid13x25Case0
  · exact grid13x25Case1
  · exact grid13x25Case2
  · exact grid13x25Case3
  · exact grid13x25Case4
  · exact grid13x25Case5
  · exact grid13x25Case6
  · exact grid13x25Case7
  · exact grid13x25Case8
  · exact grid13x25Case9
  · exact grid13x25Case10
  · exact grid13x25Case11
  · exact grid13x25Case12
  · exact grid13x25Case13
  · exact grid13x25Case14
  · exact grid13x25Case15
  · exact grid13x25Case16
  · exact grid13x25Case17
  · exact grid13x25Case18
  · exact grid13x25Case19
  · exact grid13x25Case20
  · exact grid13x25Case21
  · exact grid13x25Case22
  · exact grid13x25Case23
  · exact grid13x25Case24
  · exact grid13x25Case25
  · exact grid13x25Case26
  · exact grid13x25Case27
  · exact grid13x25Case28
  · exact grid13x25Case29
  · exact grid13x25Case30
  · exact grid13x25Case31
  · exact grid13x25Case32
  · exact grid13x25Case33
  · exact grid13x25Case34
  · exact grid13x25Case35
  · exact grid13x25Case36
  · exact grid13x25Case37
  · exact grid13x25Case38
  · exact grid13x25Case39
  · exact grid13x25Case40
  · exact grid13x25Case41
  · exact grid13x25Case42
  · exact grid13x25Case43
  · exact grid13x25Case44
  · exact grid13x25Case45
  · exact grid13x25Case46
  · exact grid13x25Case47
  · exact grid13x25Case48
  · exact grid13x25Case49



private theorem frontier_mixed_351_326_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=351) : ¬∃ f : G → ℤ, IsSDS 326 1 f :=
  abelian_short_linear G 13 27 17 1 5 2 326 1 25 2 6 23
    ⟨⟨(-7),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_559_361_36 : List RowType := [((-4),30),(1,23),(6,22),(11,27),(16,38),(21,29)]
private def stage_0_frontier_mixed_559_361_36 : Stage := [
  (((-4),30),⟨⟨0,(-298038750),0,10962000⟩,[0,0,0,1373937500,0,0,0,0,0,0,0,930050000,0],319599⟩),
  ((1,23),⟨⟨0,(-407511),0,17641⟩,[0,0,0,480740,0,0,0,0,0,0,0,480740,0],315⟩),
  ((6,22),⟨⟨0,(-127452),0,4862⟩,[0,0,0,240370,0,0,0,0,0,0,0,240370,0],105⟩),
  ((11,27),⟨⟨(-632729600),(-25951800),0,3420000⟩,[0,0,0,0,0,0,61790000,0,0,0,0,185370000,0],117401⟩),
  ((16,38),⟨⟨0,(-370617),0,15587⟩,[0,0,0,55900,0,0,0,0,0,0,0,1699360,0],315⟩),
  ((21,29),⟨⟨0,(-99502),0,5317⟩,[0,0,0,0,0,0,0,0,0,0,0,64285,0],80⟩)]
private theorem frontier_mixed_559_361_36 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=559) : ¬∃ f : G → ℤ, IsSDS 361 36 f :=
  abelian_short_mixed G 13 43 17 1 5 2 361 36 25 11 6 23 10 3
    types_frontier_mixed_559_361_36 [stage_0_frontier_mixed_559_361_36] ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_689_404_79 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=689) : ¬∃ f : G → ℤ, IsSDS 404 79 f :=
  abelian_short_linear G 13 53 17 2 5 2 404 79 25 18 6 23
    ⟨⟨(-806),(-26),25,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_689_625_300 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=689) : ¬∃ f : G → ℤ, IsSDS 625 300 f :=
  abelian_short_linear G 13 53 17 1 5 2 625 300 25 35 6 23
    ⟨⟨30,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_793_328_3 : List RowType := [((-11),25),((-11),51),((-6),30),((-6),56),((-1),29),((-1),55),(4,22),(4,48),(9,35),(9,61),(14,16),(14,42),(19,43)]
private def stage_0_frontier_mixed_793_328_3 : Stage := [
  (((-11),25),⟨⟨0,(-762073),0,37687⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],570⟩),
  (((-11),51),⟨⟨(-128466),(-7137),0,689⟩,[0,0,0,0,103090,0,0,0,0,39650,0,0,0],10⟩),
  (((-6),30),⟨⟨(-290238),(-5551),0,637⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],25⟩),
  (((-6),56),⟨⟨(-290238),(-5551),0,637⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],25⟩),
  (((-1),29),⟨⟨(-40443),2379,0,52⟩,[0,0,0,0,11895,0,0,0,0,0,0,0,0],5⟩),
  (((-1),55),⟨⟨(-2418),(-221),75,22⟩,[0,0,0,0,1300,0,0,0,0,0,0,0,0],0⟩),
  ((4,22),⟨⟨(-1378234),(-16653),0,(-3419)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],375⟩),
  ((4,48),⟨⟨(-415532),(-133224),0,9308⟩,[0,0,0,0,0,0,0,0,0,158600,0,0,0],75⟩),
  ((9,35),⟨⟨(-3907904),66612,0,8216⟩,[0,0,0,0,0,0,0,0,0,0,0,0,2854800],375⟩),
  ((9,61),⟨⟨(-672464),9516,21960,680⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],15⟩),
  ((14,16),⟨⟨(-40748),0,0,188⟩,[0,0,0,0,7320,0,0,0,0,7320,0,0,0],5⟩),
  ((14,42),⟨⟨(-2338668000),0,0,10790000⟩,[0,0,0,0,420120000,0,0,0,0,420120000,0,0,0],290583⟩),
  ((19,43),⟨⟨(-67405),0,0,481⟩,[0,0,0,0,0,0,0,10309,0,0,0,0,0],6⟩)]
private theorem frontier_mixed_793_328_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=793) : ¬∃ f : G → ℤ, IsSDS 328 3 f :=
  abelian_short_mixed G 13 61 17 2 5 2 328 3 25 4 6 23 47 10
    types_frontier_mixed_793_328_3 [stage_0_frontier_mixed_793_328_3] ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_897_400_75 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=897) : ¬∃ f : G → ℤ, IsSDS 400 75 f :=
  abelian_short_linear G 13 69 17 2 5 2 400 75 25 20 6 23
    ⟨⟨(-17628),(-7345),1695,208⟩,[0,0,35256,0,0,0,0,0,0,0,5876,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_897_452_127 : List RowType := [(11,27),(11,53),(16,38),(16,64),(21,29),(21,55),(26,26),(26,52),(31,55),(36,38),(36,64),(41,53)]
private def stage_0_frontier_mixed_897_452_127 : Stage := [
  ((11,27),⟨⟨(-3304548),0,0,(-5512)⟩,[0,0,0,0,0,3713580,0,0,0,0,0,0,0],1175⟩),
  ((11,53),⟨⟨2109744,(-292123),0,5629⟩,[0,0,0,0,0,1016600,0,0,0,0,0,0,0],125⟩),
  ((16,64),⟨⟨(-308269),0,6900,(-87)⟩,[0,0,0,0,0,0,0,0,77740,0,0,0,0],14⟩),
  ((21,29),⟨⟨(-2190474),0,50715,(-891)⟩,[0,0,0,0,0,0,0,0,0,0,107640,0,0],100⟩),
  ((21,55),⟨⟨(-2190474),0,50715,(-891)⟩,[0,0,0,0,0,0,0,0,0,0,107640,0,0],100⟩),
  ((26,26),⟨⟨0,(-28106),0,741⟩,[0,0,0,0,0,46345,0,0,0,0,0,0,0],20⟩),
  ((26,52),⟨⟨0,(-47541),0,1261⟩,[38870,0,0,0,0,92690,0,0,0,0,0,0,0],30⟩),
  ((36,38),⟨⟨0,(-79833),0,1365⟩,[941850,0,0,0,0,299598,0,0,0,0,0,0,0],82⟩),
  ((36,64),⟨⟨(-173121),0,0,(-39)⟩,[148005,0,0,0,0,0,0,0,0,0,0,0,0],20⟩),
  ((41,53),⟨⟨(-61893),0,0,13⟩,[15249,0,0,33189,0,0,0,0,0,0,0,0,0],4⟩)]
private theorem frontier_mixed_897_452_127 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=897) : ¬∃ f : G → ℤ, IsSDS 452 127 f :=
  abelian_short_mixed G 13 69 17 2 5 2 452 127 25 26 6 23 16 3
    types_frontier_mixed_897_452_127 [stage_0_frontier_mixed_897_452_127] ⟨⟨(-38),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_897_673_348 : List RowType := [(28,40),(28,66),(33,35),(33,61),(38,62),(43,43),(48,56)]
private def stage_0_frontier_mixed_897_673_348 : Stage := [
  ((28,40),⟨⟨(-10010),0,0,0⟩,[0,0,0,0,546,0,0,0,0,0,0,0,0],1⟩),
  ((28,66),⟨⟨0,0,0,(-195)⟩,[0,0,0,0,57707,0,0,0,0,0,0,0,0],32⟩),
  ((33,35),⟨⟨0,(-273),0,0⟩,[0,0,0,0,9165,0,0,0,0,0,0,0,0],1⟩),
  ((33,61),⟨⟨(-10530),0,0,0⟩,[0,0,0,0,7956,0,0,0,0,0,0,0,0],1⟩),
  ((43,43),⟨⟨0,(-2821),0,0⟩,[0,0,0,0,0,0,0,44187,0,0,0,0,0],19⟩),
  ((48,56),⟨⟨0,(-1989),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,54990],8⟩)]
private theorem frontier_mixed_897_673_348 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=897) : ¬∃ f : G → ℤ, IsSDS 673 348 f :=
  abelian_short_mixed G 13 69 17 1 5 2 673 348 25 43 6 23 16 3
    types_frontier_mixed_897_673_348 [stage_0_frontier_mixed_897_673_348] ⟨⟨38,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_897_777_452 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=897) : ¬∃ f : G → ℤ, IsSDS 777 452 f :=
  abelian_short_linear G 13 69 17 1 5 2 777 452 25 49 6 23
    ⟨⟨39,(-1),0,0⟩,[0,0,15,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1027_378_53 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1027) : ¬∃ f : G → ℤ, IsSDS 378 53 f :=
  abelian_short_linear G 13 79 17 3 5 2 378 53 25 18 6 23
    ⟨⟨(-806),(-26),25,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1027_937_612 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1027) : ¬∃ f : G → ℤ, IsSDS 937 612 f :=
  abelian_short_linear G 13 79 17 1 5 2 937 612 25 61 6 23
    ⟨⟨51,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1053_425_100 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1053) : ¬∃ f : G → ℤ, IsSDS 425 100 f :=
  abelian_short_linear G 13 81 17 2 5 2 425 100 25 25 6 23
    ⟨⟨0,(-130),75,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1053_828_503 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1053) : ¬∃ f : G → ℤ, IsSDS 828 503 f :=
  abelian_short_linear G 13 81 17 1 5 2 828 503 25 56 6 23
    ⟨⟨51,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1339_454_129 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1339) : ¬∃ f : G → ℤ, IsSDS 454 129 f :=
  abelian_short_linear G 13 103 17 1 5 2 454 129 25 32 6 23
    ⟨⟨(-53872),0,1725,(-17)⟩,[0,0,0,0,19110,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1339_961_636 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1339) : ¬∃ f : G → ℤ, IsSDS 961 636 f :=
  abelian_short_linear G 13 103 17 1 5 2 961 636 25 71 6 23
    ⟨⟨107066,(-15180),11985,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1651_394_69 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1651) : ¬∃ f : G → ℤ, IsSDS 394 69 f :=
  abelian_short_linear G 13 127 17 2 5 2 394 69 25 26 6 23
    ⟨⟨(-1547),(-156),100,3⟩,[975,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1651_1369_1044 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1651) : ¬∃ f : G → ℤ, IsSDS 1369 1044 f :=
  abelian_short_linear G 13 127 17 1 5 2 1369 1044 25 101 6 23
    ⟨⟨808,(-5),(-3),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1677_337_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1677) : ¬∃ f : G → ℤ, IsSDS 337 12 f :=
  abelian_short_linear G 13 129 17 5 5 2 337 12 25 11 6 23
    ⟨⟨(-913497),(-82576),39700,3575⟩,[0,0,0,129025,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1677_428_103 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1677) : ¬∃ f : G → ℤ, IsSDS 428 103 f :=
  abelian_short_linear G 13 129 17 0 5 2 428 103 25 32 6 23
    ⟨⟨(-6),(-1),1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1677_1273_948 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1677) : ¬∃ f : G → ℤ, IsSDS 1273 948 f :=
  abelian_short_linear G 13 129 17 0 5 2 1273 948 25 97 6 23
    ⟨⟨133042,(-10620),8385,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1807_393_68 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1807) : ¬∃ f : G → ℤ, IsSDS 393 68 f :=
  abelian_short_linear G 13 139 17 1 5 2 393 68 25 27 6 23
    ⟨⟨(-4147),0,135,(-2)⟩,[0,1690,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1807_1498_1173 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1807) : ¬∃ f : G → ℤ, IsSDS 1498 1173 f :=
  abelian_short_linear G 13 139 17 1 5 2 1498 1173 25 112 6 23
    ⟨⟨2474,(-17),(-5),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2353_337_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2353) : ¬∃ f : G → ℤ, IsSDS 337 12 f :=
  abelian_short_linear G 13 181 17 6 5 2 337 12 25 13 6 23
    ⟨⟨(-3328),(-273),125,8⟩,[650,0,0,1950,0,650,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2353_2352_2027 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2353) : ¬∃ f : G → ℤ, IsSDS 2352 2027 f :=
  abelian_short_linear G 13 181 17 1 5 2 2352 2027 25 168 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_2691_350_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2691) : ¬∃ f : G → ℤ, IsSDS 350 25 f :=
  abelian_short_linear G 13 207 17 3 5 2 350 25 25 20 6 23
    ⟨⟨(-4550),(-325),225,4⟩,[0,0,650,0,2600,0,0,0,0,0,650,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2691_2521_2196 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2691) : ¬∃ f : G → ℤ, IsSDS 2521 2196 f :=
  abelian_short_linear G 13 207 17 1 5 2 2521 2196 25 187 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4043_337_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4043) : ¬∃ f : G → ℤ, IsSDS 337 12 f :=
  abelian_short_linear G 13 311 17 4 5 2 337 12 25 17 6 23
    ⟨⟨0,(-451345700),90217431,13809540⟩,[0,0,0,0,1608129252,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4043_3938_3613 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4043) : ¬∃ f : G → ℤ, IsSDS 3938 3613 f :=
  abelian_short_linear G 13 311 17 1 5 2 3938 3613 25 294 6 23
    ⟨⟨279,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4771_334_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4771) : ¬∃ f : G → ℤ, IsSDS 334 9 f :=
  abelian_short_linear G 13 367 17 4 5 2 334 9 25 16 6 23
    ⟨⟨0,(-119),15,4⟩,[0,0,0,250,0,0,0,0,90,0,0,90,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4771_4689_4364 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4771) : ¬∃ f : G → ℤ, IsSDS 4689 4364 f :=
  abelian_short_linear G 13 367 17 1 5 2 4689 4364 25 351 6 23
    ⟨⟨341,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4953_348_23 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4953) : ¬∃ f : G → ℤ, IsSDS 348 23 f :=
  abelian_short_linear G 13 381 17 0 5 2 348 23 25 26 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4953_4625_4300 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4953) : ¬∃ f : G → ℤ, IsSDS 4625 4300 f :=
  abelian_short_linear G 13 381 17 0 5 2 4625 4300 25 355 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5031_329_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5031) : ¬∃ f : G → ℤ, IsSDS 329 4 f :=
  abelian_short_linear G 13 387 17 7 5 2 329 4 25 11 6 23
    ⟨⟨0,(-1526250),189200,52503⟩,[0,0,0,1387500,0,0,0,0,1040600,0,0,1040600,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5057_337_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5057) : ¬∃ f : G → ℤ, IsSDS 337 12 f :=
  abelian_short_linear G 13 389 17 3 5 2 337 12 25 19 6 23
    ⟨⟨(-1976),(-442),100,9⟩,[0,0,0,325,0,0,4225,0,0,0,0,2600,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5057_4900_4575 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5057) : ¬∃ f : G → ℤ, IsSDS 4900 4575 f :=
  abelian_short_linear G 13 389 17 1 5 2 4900 4575 25 370 6 23
    ⟨⟨355,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5707_342_17 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5707) : ¬∃ f : G → ℤ, IsSDS 342 17 f :=
  abelian_short_linear G 13 439 17 1 5 2 342 17 25 24 6 23
    ⟨⟨(-34),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5707_5425_5100 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5707) : ¬∃ f : G → ℤ, IsSDS 5425 5100 f :=
  abelian_short_linear G 13 439 17 1 5 2 5425 5100 25 415 6 23
    ⟨⟨400,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5759_326_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5759) : ¬∃ f : G → ℤ, IsSDS 326 1 f :=
  abelian_short_linear G 13 443 17 9 5 2 326 1 25 6 6 23
    ⟨⟨(-624),(-52),25,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7059_329_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7059) : ¬∃ f : G → ℤ, IsSDS 329 4 f :=
  abelian_short_linear G 13 543 17 6 5 2 329 4 25 13 6 23
    ⟨⟨(-104),(-169),25,4⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7059_7050_6725 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7059) : ¬∃ f : G → ℤ, IsSDS 7050 6725 f :=
  abelian_short_linear G 13 543 17 1 5 2 7050 6725 25 530 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7423_337_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7423) : ¬∃ f : G → ℤ, IsSDS 337 12 f :=
  abelian_short_linear G 13 571 17 1 5 2 337 12 25 23 6 23
    ⟨⟨(-20),(-1),1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7423_7162_6837 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7423) : ¬∃ f : G → ℤ, IsSDS 7162 6837 f :=
  abelian_short_linear G 13 571 17 1 5 2 7162 6837 25 548 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12129_329_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12129) : ¬∃ f : G → ℤ, IsSDS 329 4 f :=
  abelian_short_linear G 13 933 17 4 5 2 329 4 25 17 6 23
    ⟨⟨12,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12129_12016_11691 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12129) : ¬∃ f : G → ℤ, IsSDS 12016 11691 f :=
  abelian_short_linear G 13 933 17 1 5 2 12016 11691 25 916 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14313_328_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14313) : ¬∃ f : G → ℤ, IsSDS 328 3 f :=
  abelian_short_linear G 13 1101 17 4 5 2 328 3 25 16 6 23
    ⟨⟨0,0,441,(-127)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14313_14225_13900 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14313) : ¬∃ f : G → ℤ, IsSDS 14225 13900 f :=
  abelian_short_linear G 13 1101 17 1 5 2 14225 13900 25 1085 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15171_329_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15171) : ¬∃ f : G → ℤ, IsSDS 329 4 f :=
  abelian_short_linear G 13 1167 17 3 5 2 329 4 25 19 6 23
    ⟨⟨9,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15171_15006_14681 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15171) : ¬∃ f : G → ℤ, IsSDS 15006 14681 f :=
  abelian_short_linear G 13 1167 17 1 5 2 15006 14681 25 1148 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_18551_329_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=18551) : ¬∃ f : G → ℤ, IsSDS 329 4 f :=
  abelian_short_linear G 13 1427 17 2 5 2 329 4 25 21 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_18551_18334_18009 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=18551) : ¬∃ f : G → ℤ, IsSDS 18334 18009 f :=
  abelian_short_linear G 13 1427 17 1 5 2 18334 18009 25 1406 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_22269_329_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=22269) : ¬∃ f : G → ℤ, IsSDS 329 4 f :=
  abelian_short_linear G 13 1713 17 1 5 2 329 4 25 23 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_22269_22000_21675 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=22269) : ¬∃ f : G → ℤ, IsSDS 22000 21675 f :=
  abelian_short_linear G 13 1713 17 1 5 2 22000 21675 25 1690 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_24011_326_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=24011) : ¬∃ f : G → ℤ, IsSDS 326 1 f :=
  abelian_short_linear G 13 1847 17 6 5 2 326 1 25 12 6 23
    ⟨⟨(-546),(-13),15,0⟩,[0,0,130,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_42939_326_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=42939) : ¬∃ f : G → ℤ, IsSDS 326 1 f :=
  abelian_short_linear G 13 3303 17 4 5 2 326 1 25 16 6 23
    ⟨⟨1,0,0,(-1)⟩,[0,0,0,255,0,0,35,0,0,0,0,120,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_42939_42849_42524 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=42939) : ¬∃ f : G → ℤ, IsSDS 42849 42524 f :=
  abelian_short_linear G 13 3303 17 1 5 2 42849 42524 25 3287 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_54431_326_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=54431) : ¬∃ f : G → ℤ, IsSDS 326 1 f :=
  abelian_short_linear G 13 4187 17 3 5 2 326 1 25 18 6 23
    ⟨⟨8,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_54431_54289_53964 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=54431) : ¬∃ f : G → ℤ, IsSDS 54289 53964 f :=
  abelian_short_linear G 13 4187 17 1 5 2 54289 53964 25 4169 6 23
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_13_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=13*m)
    (hm : 13 < m) (hn : k-l=(13:ℤ)*25) : False := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_13_25
  simp only [keep_13_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=326 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_351_326_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=361 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_559_361_36 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=404 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_689_404_79 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_689_625_300 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=328 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_793_328_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=400 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_897_400_75 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=452 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_897_452_127 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=673 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_897_673_348 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=777 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_897_777_452 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=378 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1027_378_53 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=937 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1027_937_612 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=425 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1053_425_100 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=828 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1053_828_503 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=454 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1339_454_129 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=961 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1339_961_636 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=394 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1651_394_69 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1369 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1651_1369_1044 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=337 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1677_337_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=428 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1677_428_103 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1273 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1677_1273_948 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=393 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1807_393_68 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1498 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1807_1498_1173 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=337 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2353_337_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2352 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2353_2352_2027 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=326 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2379_326_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=350 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2691_350_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2521 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2691_2521_2196 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=337 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4043_337_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3938 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4043_3938_3613 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=334 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4771_334_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4689 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4771_4689_4364 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=348 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4953_348_23 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4953_4625_4300 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=329 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5031_329_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=337 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5057_337_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4900 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5057_4900_4575 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=342 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5707_342_17 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5425 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5707_5425_5100 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=326 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5759_326_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=329 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7059_329_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7050 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7059_7050_6725 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=337 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7423_337_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7162 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7423_7162_6837 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=329 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12129_329_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=12016 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12129_12016_11691 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=328 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14313_328_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=14225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14313_14225_13900 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=329 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15171_329_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=15006 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15171_15006_14681 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=329 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_18551_329_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=18334 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_18551_18334_18009 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=329 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_22269_329_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=22000 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_22269_22000_21675 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=326 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_24011_326_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=326 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_42939_326_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=42849 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_42939_42849_42524 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=326 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_54431_326_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=54289 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_54431_54289_53964 G hg ⟨f,hf⟩

end Signed39.Contraction
