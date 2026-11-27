import Signed25Grid19Part0
import Signed25Grid19Part12
import Signed25Grid19Part24
import Signed25Grid19Part36
import Signed25Grid19Part48
import SignedOrbit19Cofactor25
import SignedOrbit19Cofactor25
import Signed25Case1539W850
import Signed25Case1767W478
import Signed25Case1919W550
import Signed25Case3363W493
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_19_25 : divisorGrid 19 25 214 qInputs_19_25 keep_19_25 := by
  intro d
  fin_cases d
  · exact grid19x25Case0
  · exact grid19x25Case1
  · exact grid19x25Case2
  · exact grid19x25Case3
  · exact grid19x25Case4
  · exact grid19x25Case5
  · exact grid19x25Case6
  · exact grid19x25Case7
  · exact grid19x25Case8
  · exact grid19x25Case9
  · exact grid19x25Case10
  · exact grid19x25Case11
  · exact grid19x25Case12
  · exact grid19x25Case13
  · exact grid19x25Case14
  · exact grid19x25Case15
  · exact grid19x25Case16
  · exact grid19x25Case17
  · exact grid19x25Case18
  · exact grid19x25Case19
  · exact grid19x25Case20
  · exact grid19x25Case21
  · exact grid19x25Case22
  · exact grid19x25Case23
  · exact grid19x25Case24
  · exact grid19x25Case25
  · exact grid19x25Case26
  · exact grid19x25Case27
  · exact grid19x25Case28
  · exact grid19x25Case29
  · exact grid19x25Case30
  · exact grid19x25Case31
  · exact grid19x25Case32
  · exact grid19x25Case33
  · exact grid19x25Case34
  · exact grid19x25Case35
  · exact grid19x25Case36
  · exact grid19x25Case37
  · exact grid19x25Case38
  · exact grid19x25Case39
  · exact grid19x25Case40
  · exact grid19x25Case41
  · exact grid19x25Case42
  · exact grid19x25Case43
  · exact grid19x25Case44
  · exact grid19x25Case45
  · exact grid19x25Case46
  · exact grid19x25Case47
  · exact grid19x25Case48
  · exact grid19x25Case49



private def types_frontier_mixed_589_484_9 : List RowType := [((-9),21),((-6),22),((-5),29),((-1),27),(0,0),(1,27),(5,29),(6,22),(9,21)]
private def stage_0_frontier_mixed_589_484_9 : Stage := [
  (((-9),21),⟨⟨0,0,(-25069000),4381875⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],454157⟩),
  (((-6),22),⟨⟨0,(-68324),(-47802),4658⟩,[0,0,0,0,0,290966,819888,0,0,0,0,0,0,0,0,0,0,0,0],297⟩),
  (((-5),29),⟨⟨0,0,(-224460000),(-38617500)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],6420803⟩),
  (((-1),27),⟨⟨(-232500),0,0,(-7500)⟩,[232500,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],341⟩),
  ((0,0),⟨⟨4617,(-76),(-168),(-5)⟩,[0,0,0,0,0,760,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩),
  ((1,27),⟨⟨(-232500),0,0,(-7500)⟩,[232500,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],341⟩),
  ((5,29),⟨⟨0,0,(-224460000),(-38617500)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],6420803⟩),
  ((6,22),⟨⟨0,(-68324),(-47802),4658⟩,[0,0,0,0,0,290966,819888,0,0,0,0,0,0,0,0,0,0,0,0],297⟩),
  ((9,21),⟨⟨0,0,(-25069000),4381875⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],454157⟩)]
private theorem frontier_mixed_589_484_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=589) : ¬∃ f : G → ℤ, IsSDS 484 9 f :=
  abelian_short_mixed G 19 31 21 1 1 0 484 9 25 4 8 21 18 11
    types_frontier_mixed_589_484_9 [stage_0_frontier_mixed_589_484_9] ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1121_529_54 : List RowType := [((-8),32),((-7),53),((-6),56),((-5),41),((-4),46),((-3),33),((-2),40),((-1),29),(0,0),(0,38),(1,29),(2,40),(3,33),(4,46),(5,41),(6,56),(7,53),(8,32),(9,31),(10,50),(11,51),(12,34),(13,37),(14,22),(15,27),(16,52),(18,48),(19,57),(20,48),(22,52),(25,37),(26,34),(28,50),(31,53)]
private def stage_0_frontier_mixed_1121_529_54 : Stage := [
  (((-7),53),⟨⟨0,(-34279),531,1144⟩,[0,0,0,3540,0,0,16992,0,0,0,0,0,0,0,0,0,0,0,0],33⟩),
  (((-6),56),⟨⟨0,(-845234),49855,33127⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,3109654,1181534,0,0,0,0],395⟩),
  (((-5),41),⟨⟨0,(-236531),46551,4018⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49324,0,0],132⟩),
  (((-4),46),⟨⟨0,(-377777),48085,12523⟩,[0,0,0,0,0,0,0,0,0,330695,0,0,0,0,0,0,0,0,0],110⟩),
  (((-2),40),⟨⟨0,(-3363),0,171⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  (((-1),29),⟨⟨(-2235274),(-95285),16697,1066⟩,[2235274,0,381140,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],430⟩),
  ((1,29),⟨⟨(-2235274),(-95285),16697,1066⟩,[2235274,0,381140,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],430⟩),
  ((2,40),⟨⟨0,(-3363),0,171⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((5,41),⟨⟨0,(-236531),46551,4018⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49324,0,0],132⟩),
  ((6,56),⟨⟨0,(-193933),42185,5004⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],104⟩),
  ((7,53),⟨⟨0,(-34279),531,1144⟩,[0,0,0,3540,0,0,16992,0,0,0,0,0,0,0,0,0,0,0,0],33⟩),
  ((8,32),⟨⟨0,(-163666),18290,4839⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,521265,0,0,0],110⟩),
  ((9,31),⟨⟨0,(-642333),87025,18836⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1726340,0,0,0],316⟩),
  ((10,50),⟨⟨0,(-152456),25665,3517⟩,[0,0,0,0,0,0,0,0,0,0,0,0,195054,0,0,0,0,0,0],80⟩),
  ((11,51),⟨⟨0,(-366567),78647,7958⟩,[0,0,0,0,0,0,0,0,0,91922,0,0,0,0,1262246,0,0,0,0],113⟩),
  ((12,34),⟨⟨0,(-93043),10443,2806⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,262314,0,0,0,0,0],40⟩),
  ((13,37),⟨⟨0,(-212990),15871,8851⟩,[0,0,0,0,0,0,0,0,0,0,0,0,603098,0,0,0,0,0,0],64⟩),
  ((15,27),⟨⟨0,(-536959),0,19399⟩,[0,0,0,0,0,0,0,0,1138936,753312,0,0,0,0,0,0,0,0,0],600⟩),
  ((16,52),⟨⟨0,(-134520),10797,4605⟩,[0,0,0,0,0,0,0,0,0,0,123310,0,217474,0,0,369930,0,0,0],53⟩),
  ((18,48),⟨⟨0,(-1853013),246561,53220⟩,[0,0,0,0,0,0,0,0,0,351994,0,0,0,3954888,0,4264284,0,0,0],632⟩),
  ((19,57),⟨⟨0,(-1121),0,19⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((26,34),⟨⟨0,(-3363),0,19⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],9⟩),
  ((28,50),⟨⟨0,(-448400),43778,12140⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,2495346,0,0,0,0],203⟩)]
private theorem frontier_mixed_1121_529_54 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1121) : ¬∃ f : G → ℤ, IsSDS 529 54 f :=
  abelian_short_mixed G 19 59 21 1 1 0 529 54 25 13 8 21 28 9
    types_frontier_mixed_1121_529_54 [stage_0_frontier_mixed_1121_529_54] ⟨⟨0,(-2204),160,91⟩,[0,0,0,513,0,0,0,0,0,0,0,0,0,0,9500,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1273_577_102 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1273) : ¬∃ f : G → ℤ, IsSDS 577 102 f :=
  abelian_short_linear G 19 67 21 1 1 0 577 102 25 19 8 21
    ⟨⟨0,(-38),9,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1273_1128_653 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1273) : ¬∃ f : G → ℤ, IsSDS 1128 653 f :=
  abelian_short_linear G 19 67 21 1 1 0 1128 653 25 48 8 21
    ⟨⟨8195849772,(-320328558),(-32300125),3437460⟩,[0,974462280,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,366978348,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1349_784_309 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1349) : ¬∃ f : G → ℤ, IsSDS 784 309 f :=
  abelian_short_linear G 19 71 21 1 1 0 784 309 25 34 8 21
    ⟨⟨1178,(-76),5,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1349_841_366 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1349) : ¬∃ f : G → ℤ, IsSDS 841 366 f :=
  abelian_short_linear G 19 71 21 1 1 0 841 366 25 37 8 21
    ⟨⟨1178,(-76),5,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1501_625_150 : List RowType := [(4,56),(5,59),(6,50),(7,29),(7,67),(8,34),(8,72),(9,27),(9,65),(10,46),(11,53),(12,48),(13,31),(13,69),(14,40),(14,78),(15,37),(15,75),(16,22),(16,60),(17,33),(17,71),(18,32),(18,70),(19,57),(20,32),(20,70),(21,33),(21,71),(22,60),(23,37),(23,75),(24,40),(24,78),(25,69),(26,48),(27,53),(28,46),(29,65),(30,34),(30,72),(31,67),(32,50),(33,59),(34,56),(35,41),(36,52),(37,51),(38,38),(38,76),(39,51),(40,52),(41,41),(42,56),(43,59),(44,50),(46,72)]
private def stage_0_frontier_mixed_1501_625_150 : Stage := [
  ((6,50),⟨⟨(-2809872),(-186124),89191,2823⟩,[0,1984322,0,0,0,0,0,0,0,0,0,1984322,0,0,0,0,0,0,0],193⟩),
  ((9,27),⟨⟨0,(-535857),0,10602⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,800033,3922113,0,0,0,0],1495⟩),
  ((11,53),⟨⟨(-2240598),66281,18881,(-1544)⟩,[0,0,0,0,243794,0,0,0,451406,0,0,0,0,0,0,0,0,0,0],84⟩),
  ((14,40),⟨⟨(-987658),(-250667),77973,4314⟩,[0,0,987658,0,0,0,0,0,0,0,0,231154,0,0,0,0,0,0,0],182⟩),
  ((14,78),⟨⟨3458,(-432),75,7⟩,[0,0,52,0,0,0,0,0,0,0,0,652,0,0,0,0,12,0,0],0⟩),
  ((15,75),⟨⟨46452,(-13193),0,131⟩,[0,3318,0,0,0,3318,0,0,0,0,0,0,0,0,0,0,0,0,0],23⟩),
  ((16,22),⟨⟨(-562875),0,0,171⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,118579,0,0,382755,0,0],92⟩),
  ((16,60),⟨⟨180120,(-28519),9243,244⟩,[0,0,0,0,0,0,0,0,0,0,0,66044,0,0,0,0,0,0,0],7⟩),
  ((18,32),⟨⟨(-7441958),0,132483,(-1468)⟩,[0,918612,0,0,2805369,0,0,0,0,0,0,129086,0,1616577,214643,0,0,30020,0],345⟩),
  ((18,70),⟨⟨(-13316872),0,482058,(-9560)⟩,[0,0,0,0,0,0,0,0,0,0,0,1185790,0,0,0,0,0,0,0],363⟩),
  ((19,57),⟨⟨(-345230),0,0,(-532)⟩,[0,0,0,0,63042,0,0,0,0,0,0,0,0,0,0,0,0,0,0],51⟩),
  ((20,70),⟨⟨(-1855236),0,22436,(-968)⟩,[0,0,0,0,0,0,297198,0,0,630420,0,0,0,0,0,111074,0,0,111074],161⟩),
  ((29,65),⟨⟨(-2143428),0,75129,(-1521)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],70⟩),
  ((30,34),⟨⟨0,0,0,(-450165177)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],39898160⟩),
  ((32,50),⟨⟨1176784,(-153102),30968,1945⟩,[72048,31521,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],32⟩),
  ((33,59),⟨⟨(-54036),(-165110),46215,2455⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,447298,54036,567378],63⟩),
  ((34,56),⟨⟨(-6130084),0,87216,(-914)⟩,[0,0,1996330,0,0,0,252168,0,801534,0,378252,0,0,0,0,0,0,729486,0],291⟩),
  ((38,76),⟨⟨(-306204),(-246164),0,6251⟩,[192128,247665,0,0,90060,43529,0,0,0,0,0,0,0,0,0,0,43529,90060,139593],102⟩),
  ((40,52),⟨⟨126084,(-96064),0,2375⟩,[0,0,0,0,0,0,0,0,0,13509,49533,0,0,66044,0,0,49533,0,0],64⟩),
  ((41,41),⟨⟨0,(-3002),0,76⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((43,59),⟨⟨(-1056704),0,13983,431⟩,[0,0,0,0,162108,0,0,0,0,0,0,0,0,0,0,0,0,0,111074],51⟩),
  ((44,50),⟨⟨(-5526682),0,111390,(-422)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,1909272,36024,0,0,0,0],159⟩)]
private theorem frontier_mixed_1501_625_150 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1501) : ¬∃ f : G → ℤ, IsSDS 625 150 f :=
  abelian_short_mixed G 19 79 21 1 1 0 625 150 25 25 8 21 25 6
    types_frontier_mixed_1501_625_150 [stage_0_frontier_mixed_1501_625_150] ⟨⟨(-6308),(-513),375,8⟩,[0,1368,1178,0,0,0,0,0,0,0,0,0,0,0,0,0,0,342,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1501_1176_701 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1501) : ¬∃ f : G → ℤ, IsSDS 1176 701 f :=
  abelian_short_linear G 19 79 21 1 1 0 1176 701 25 54 8 21
    ⟨⟨21648,(-933),77,8⟩,[0,0,0,0,0,0,66,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private def types_frontier_mixed_1539_869_394 : List RowType := [(20,42),(20,80),(21,35),(21,73),(22,36),(22,74),(23,45),(24,62),(25,49),(26,44),(27,47),(28,58),(29,39),(29,77),(30,66),(31,63),(32,68),(33,43),(34,64),(35,55),(36,54),(37,61),(38,38),(38,76),(39,61),(40,54),(41,55),(42,64),(43,43),(44,68),(47,77),(48,58),(52,62),(55,73)]
private def stage_0_frontier_mixed_1539_869_394 : Stage := [
  ((20,42),⟨⟨(-423225),0,0,(-247)⟩,[0,53865,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],80⟩),
  ((20,80),⟨⟨(-996417),0,20844,(-251)⟩,[68229,127737,125856,94392,0,65664,16416,14877,0,0,0,0,0,0,0,0,0,0,0],16⟩),
  ((21,73),⟨⟨0,0,10584,(-1467)⟩,[0,0,0,0,0,0,615600,0,571995,0,0,0,0,0,0,0,0,0,0],176⟩),
  ((22,36),⟨⟨(-120384),0,2268,(-28)⟩,[0,0,31122,0,0,0,0,10260,0,0,0,0,0,0,0,0,0,10260,0],5⟩),
  ((22,74),⟨⟨(-120384),0,2268,(-28)⟩,[0,0,31122,0,0,0,0,10260,0,0,0,0,0,0,0,0,0,10260,0],5⟩),
  ((23,45),⟨⟨(-200070),0,6885,(-85)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],2⟩),
  ((24,62),⟨⟨(-698706),0,18225,(-225)⟩,[0,0,0,0,0,0,0,0,6156,0,83106,0,0,0,83106,0,0,0,0],11⟩),
  ((25,49),⟨⟨0,0,0,(-437)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,106704,0,0,0,0],64⟩),
  ((27,47),⟨⟨(-1745226),0,59049,(-729)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],20⟩),
  ((31,63),⟨⟨(-15732),0,0,0⟩,[0,2242,0,1102,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((33,43),⟨⟨3026746035,0,0,(-4151915)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1114947⟩),
  ((34,64),⟨⟨(-1593720),0,58941,(-1399)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1014714,0,0,0,0],98⟩),
  ((35,55),⟨⟨(-348840),0,9315,(-115)⟩,[0,0,0,0,0,0,0,0,0,0,49248,0,0,0,49248,0,0,0,0],11⟩),
  ((36,54),⟨⟨(-2253096),0,68040,(-1296)⟩,[0,0,0,0,0,184680,0,0,0,0,0,0,0,0,0,0,0,258552,0],125⟩),
  ((37,61),⟨⟨(-101574),0,1620,(-20)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],7⟩),
  ((38,38),⟨⟨0,0,230040,(-8540)⟩,[0,0,0,461700,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],817⟩),
  ((38,76),⟨⟨271206,0,33561,(-1301)⟩,[0,0,0,0,0,359100,0,0,0,0,0,0,0,0,0,0,0,0,0],46⟩),
  ((39,61),⟨⟨249318,0,0,(-342)⟩,[0,0,0,0,0,138510,0,0,0,0,0,0,0,0,0,0,0,0,0],55⟩),
  ((42,64),⟨⟨249318,0,0,(-342)⟩,[0,0,0,0,0,138510,0,0,0,0,0,0,0,0,0,0,0,0,0],55⟩),
  ((43,43),⟨⟨0,0,230040,(-8540)⟩,[0,0,0,461700,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],817⟩),
  ((44,68),⟨⟨(-101574),0,1620,(-20)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],7⟩),
  ((47,77),⟨⟨(-1593720),0,58941,(-1399)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1014714,0,0,0,0],98⟩)]
private theorem frontier_mixed_1539_869_394 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1539) : ¬∃ f : G → ℤ, IsSDS 869 394 f :=
  abelian_short_mixed G 19 81 21 1 1 0 869 394 25 41 8 21 64 15
    types_frontier_mixed_1539_869_394 [stage_0_frontier_mixed_1539_869_394] ⟨⟨(-2254),0,77,(-1)⟩,[0,0,0,0,0,0,0,0,0,0,92,0,0,0,184,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_1767_725_250 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1767) : ¬∃ f : G → ℤ, IsSDS 725 250 f :=
  abelian_short_linear G 19 93 21 1 1 0 725 250 25 35 8 21
    ⟨⟨876,(-76),13,1⟩,[74,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1767_1162_687 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1767) : ¬∃ f : G → ℤ, IsSDS 1162 687 f :=
  abelian_short_linear G 19 93 21 1 1 0 1162 687 25 58 8 21
    ⟨⟨3666,(-136),13,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,74,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_1919_1709_1234 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1919) : ¬∃ f : G → ℤ, IsSDS 1709 1234 f :=
  abelian_short_linear G 19 101 21 1 1 0 1709 1234 25 81 8 21
    ⟨⟨122816,(-2679),(-153),16⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,798,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1957_688_213 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1957) : ¬∃ f : G → ℤ, IsSDS 688 213 f :=
  abelian_short_linear G 19 103 21 1 1 0 688 213 25 34 8 21
    ⟨⟨0,(-247),155,2⟩,[608,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1957_1353_878 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1957) : ¬∃ f : G → ℤ, IsSDS 1353 878 f :=
  abelian_short_linear G 19 103 21 1 1 0 1353 878 25 69 8 21
    ⟨⟨34200,(-1163),221,6⟩,[0,0,0,0,0,0,0,0,1680,0,0,0,906,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2413_628_153 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2413) : ¬∃ f : G → ℤ, IsSDS 628 153 f :=
  abelian_short_linear G 19 127 21 0 1 0 628 153 25 32 8 21
    ⟨⟨816,(-343),225,2⟩,[780,294,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2413_1825_1350 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2413) : ¬∃ f : G → ℤ, IsSDS 1825 1350 f :=
  abelian_short_linear G 19 127 21 0 1 0 1825 1350 25 95 8 21
    ⟨⟨37574,(-825),45,4⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,162,46,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_3363_3362_2887 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3363) : ¬∃ f : G → ℤ, IsSDS 3362 2887 f :=
  abelian_short_linear G 19 177 21 0 1 0 3362 2887 25 164 8 21
    ⟨⟨(-177),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3401_536_61 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3401) : ¬∃ f : G → ℤ, IsSDS 536 61 f :=
  abelian_short_linear G 19 179 21 2 1 0 536 61 25 24 8 21
    ⟨⟨(-49856),1368,1122,(-31)⟩,[0,0,0,0,0,0,0,285,0,0,0,0,0,285,0,0,0,3021,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3401_3025_2550 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3401) : ¬∃ f : G → ℤ, IsSDS 3025 2550 f :=
  abelian_short_linear G 19 179 21 1 1 0 3025 2550 25 155 8 21
    ⟨⟨150,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3819_509_34 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3819) : ¬∃ f : G → ℤ, IsSDS 509 34 f :=
  abelian_short_linear G 19 201 21 3 1 0 509 34 25 19 8 21
    ⟨⟨0,(-969),189,26⟩,[0,0,0,418,0,342,0,0,418,0,0,0,0,76,532,0,532,76,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3819_3606_3131 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3819) : ¬∃ f : G → ℤ, IsSDS 3606 3131 f :=
  abelian_short_linear G 19 201 21 1 1 0 3606 3131 25 182 8 21
    ⟨⟨34170,(-371),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4237_537_62 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4237) : ¬∃ f : G → ℤ, IsSDS 537 62 f :=
  abelian_short_linear G 19 223 21 0 1 0 537 62 25 27 8 21
    ⟨⟨(-49666),0,1711,(-15)⟩,[0,0,0,0,4560,0,0,5054,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4237_3748_3273 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4237) : ¬∃ f : G → ℤ, IsSDS 3748 3273 f :=
  abelian_short_linear G 19 223 21 0 1 0 3748 3273 25 196 8 21
    ⟨⟨96277095,(-1296792),750820,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4503_525_50 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4503) : ¬∃ f : G → ℤ, IsSDS 525 50 f :=
  abelian_short_linear G 19 237 21 1 1 0 525 50 25 25 8 21
    ⟨⟨0,(-482),140,9⟩,[0,1000,0,0,0,0,0,0,433,0,0,0,0,0,0,0,0,0,720],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4503_4078_3603 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4503) : ¬∃ f : G → ℤ, IsSDS 4078 3603 f :=
  abelian_short_linear G 19 237 21 1 1 0 4078 3603 25 212 8 21
    ⟨⟨38025,0,0,(-1)⟩,[0,0,0,0,0,0,391,0,0,1576,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5757_500_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5757) : ¬∃ f : G → ℤ, IsSDS 500 25 f :=
  abelian_short_linear G 19 303 21 3 1 0 500 25 25 20 8 21
    ⟨⟨0,(-1292),240,31⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,4332,2565,1216,285,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5757_5497_5022 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5757) : ¬∃ f : G → ℤ, IsSDS 5497 5022 f :=
  abelian_short_linear G 19 303 21 1 1 0 5497 5022 25 283 8 21
    ⟨⟨82113,(-574),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7201_481_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7201) : ¬∃ f : G → ℤ, IsSDS 481 6 f :=
  abelian_short_linear G 19 379 21 7 1 0 481 6 25 11 8 21
    ⟨⟨0,(-3610),375,109⟩,[0,0,0,0,0,0,0,0,0,0,0,646,0,0,2926,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7543_478_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7543) : ¬∃ f : G → ℤ, IsSDS 478 3 f :=
  abelian_short_linear G 19 397 21 8 1 0 478 3 25 8 8 21
    ⟨⟨0,(-150546500),22674600,6008769⟩,[0,0,0,0,0,0,0,0,0,72981000,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8607_477_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8607) : ¬∃ f : G → ℤ, IsSDS 477 2 f :=
  abelian_short_linear G 19 453 21 9 1 0 477 2 25 7 8 21
    ⟨⟨(-122),(-50),9,1⟩,[122,0,2,0,0,0,0,0,80,50,0,2,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10089_481_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10089) : ¬∃ f : G → ℤ, IsSDS 481 6 f :=
  abelian_short_linear G 19 531 21 6 1 0 481 6 25 13 8 21
    ⟨⟨0,(-17936),1575,473⟩,[0,0,0,3876,0,0,0,0,0,11286,0,0,14820,456,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10089_10076_9601 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10089) : ¬∃ f : G → ℤ, IsSDS 10076 9601 f :=
  abelian_short_linear G 19 531 21 0 1 0 10076 9601 25 518 8 21
    ⟨⟨(-531),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10583_493_18 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10583) : ¬∃ f : G → ℤ, IsSDS 493 18 f :=
  abelian_short_linear G 19 557 21 1 1 0 493 18 25 23 8 21
    ⟨⟨0,(-1655),516,17⟩,[0,0,0,0,4820,0,0,0,3912,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10583_10202_9727 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10583) : ¬∃ f : G → ℤ, IsSDS 10202 9727 f :=
  abelian_short_linear G 19 557 21 1 1 0 10202 9727 25 534 8 21
    ⟨⟨514,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12521_476_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12521) : ¬∃ f : G → ℤ, IsSDS 476 1 f :=
  abelian_short_linear G 19 659 21 9 1 0 476 1 25 6 8 21
    ⟨⟨0,(-266),49,5⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_17309_481_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=17309) : ¬∃ f : G → ℤ, IsSDS 481 6 f :=
  abelian_short_linear G 19 911 21 4 1 0 481 6 25 17 8 21
    ⟨⟨(-627),(-266),24,5⟩,[627,0,323,0,171,0,171,0,323,0,0,0,171,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_17309_17144_16669 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=17309) : ¬∃ f : G → ℤ, IsSDS 17144 16669 f :=
  abelian_short_linear G 19 911 21 1 1 0 17144 16669 25 894 8 21
    ⟨⟨(-911),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_19361_484_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=19361) : ¬∃ f : G → ℤ, IsSDS 484 9 f :=
  abelian_short_linear G 19 1019 21 1 1 0 484 9 25 22 8 21
    ⟨⟨43,(-44),0,1⟩,[0,0,41,80,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_19361_19009_18534 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=19361) : ¬∃ f : G → ℤ, IsSDS 19009 18534 f :=
  abelian_short_linear G 19 1019 21 1 1 0 19009 18534 25 997 8 21
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_21603_477_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=21603) : ¬∃ f : G → ℤ, IsSDS 477 2 f :=
  abelian_short_linear G 19 1137 21 7 1 0 477 2 25 11 8 21
    ⟨⟨(-875797500),(-163138750),28470000,1504311⟩,[875797500,326277500,515175000,360622500,0,103035000,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_22629_476_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=22629) : ¬∃ f : G → ℤ, IsSDS 476 1 f :=
  abelian_short_linear G 19 1191 21 8 1 0 476 1 25 8 8 21
    ⟨⟨(-16929),(-912),540,(-43)⟩,[16929,0,0,5472,0,2584,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_30267_477_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=30267) : ¬∃ f : G → ℤ, IsSDS 477 2 f :=
  abelian_short_linear G 19 1593 21 6 1 0 477 2 25 13 8 21
    ⟨⟨(-127072),(-24738),4095,(-41)⟩,[127072,49476,78432,58330,0,26562,14896,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_30267_30250_29775 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=30267) : ¬∃ f : G → ℤ, IsSDS 30250 29775 f :=
  abelian_short_linear G 19 1593 21 0 1 0 30250 29775 25 1580 8 21
    ⟨⟨(-1593),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_31749_481_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=31749) : ¬∃ f : G → ℤ, IsSDS 481 6 f :=
  abelian_short_linear G 19 1671 21 1 1 0 481 6 25 23 8 21
    ⟨⟨2,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_31749_31356_30881 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=31749) : ¬∃ f : G → ℤ, IsSDS 31356 30881 f :=
  abelian_short_linear G 19 1671 21 1 1 0 31356 30881 25 1648 8 21
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_51509_476_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=51509) : ¬∃ f : G → ℤ, IsSDS 476 1 f :=
  abelian_short_linear G 19 2711 21 6 1 0 476 1 25 12 8 21
    ⟨⟨(-193116),(-20995),4950,(-391)⟩,[193116,11552,0,125970,45752,0,0,7790,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_51927_477_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=51927) : ¬∃ f : G → ℤ, IsSDS 477 2 f :=
  abelian_short_linear G 19 2733 21 4 1 0 477 2 25 17 8 21
    ⟨⟨0,0,32,(-59)⟩,[0,0,0,0,0,0,0,0,0,779,1292,2755,0,4883,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_51927_51758_51283 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=51927) : ¬∃ f : G → ℤ, IsSDS 51758 51283 f :=
  abelian_short_linear G 19 2733 21 1 1 0 51758 51283 25 2716 8 21
    ⟨⟨(-2733),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_58083_478_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=58083) : ¬∃ f : G → ℤ, IsSDS 478 3 f :=
  abelian_short_linear G 19 3057 21 1 1 0 478 3 25 22 8 21
    ⟨⟨2,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_58083_57725_57250 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=58083) : ¬∃ f : G → ℤ, IsSDS 57725 57250 f :=
  abelian_short_linear G 19 3057 21 1 1 0 57725 57250 25 3035 8 21
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_95247_477_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=95247) : ¬∃ f : G → ℤ, IsSDS 477 2 f :=
  abelian_short_linear G 19 5013 21 1 1 0 477 2 25 23 8 21
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_95247_94850_94375 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=95247) : ¬∃ f : G → ℤ, IsSDS 94850 94375 f :=
  abelian_short_linear G 19 5013 21 1 1 0 94850 94375 25 4990 8 21
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_116489_476_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=116489) : ¬∃ f : G → ℤ, IsSDS 476 1 f :=
  abelian_short_linear G 19 6131 21 3 1 0 476 1 25 18 8 21
    ⟨⟨0,0,0,(-1)⟩,[0,1,4,9,16,25,36,49,64,81,0,0,0,0,0,0,9,4,1],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_116489_116281_115806 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=116489) : ¬∃ f : G → ℤ, IsSDS 116281 115806 f :=
  abelian_short_linear G 19 6131 21 1 1 0 116281 115806 25 6113 8 21
    ⟨⟨(-6131),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_174249_476_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=174249) : ¬∃ f : G → ℤ, IsSDS 476 1 f :=
  abelian_short_linear G 19 9171 21 1 1 0 476 1 25 22 8 21
    ⟨⟨2,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_174249_173889_173414 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=174249) : ¬∃ f : G → ℤ, IsSDS 173889 173414 f :=
  abelian_short_linear G 19 9171 21 1 1 0 173889 173414 25 9149 8 21
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_19_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=19*m)
    (hm : 19 < m) (hn : k-l=(19:ℤ)*25) : False := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_19_25
  simp only [keep_19_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=484 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_589_484_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=529 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1121_529_54 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=577 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1273_577_102 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1128 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1273_1128_653 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=784 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1349_784_309 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=841 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1349_841_366 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1501_625_150 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1501_1176_701 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=850 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1539_850_375 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=869 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1539_869_394 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=478 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1767_478_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=725 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1767_725_250 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1162 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1767_1162_687 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=550 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1919_550_75 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1709 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1919_1709_1234 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=688 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1957_688_213 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1353 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1957_1353_878 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=628 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2413_628_153 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1825 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2413_1825_1350 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=481 := by omega
    rw [hk,hL] at hf
    exact Signed39.Shape.no_2869_481_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=493 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3363_493_18 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3362 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3363_3362_2887 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=536 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3401_536_61 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3401_3025_2550 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=509 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3819_509_34 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3606 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3819_3606_3131 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=537 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4237_537_62 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3748 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4237_3748_3273 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=525 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4503_525_50 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4078 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4503_4078_3603 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=476 := by omega
    rw [hk,hL] at hf
    exact Signed39.Shape.no_5301_476_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=500 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5757_500_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5497 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5757_5497_5022 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=481 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7201_481_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=478 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7543_478_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=477 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8607_477_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=481 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10089_481_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=10076 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10089_10076_9601 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=493 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10583_493_18 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=10202 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10583_10202_9727 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=476 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12521_476_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=481 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_17309_481_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=17144 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_17309_17144_16669 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=484 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_19361_484_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=19009 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_19361_19009_18534 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=477 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_21603_477_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=476 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_22629_476_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=477 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_30267_477_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=30250 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_30267_30250_29775 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=481 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_31749_481_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=31356 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_31749_31356_30881 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=476 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_51509_476_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=477 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_51927_477_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=51758 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_51927_51758_51283 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=478 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_58083_478_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=57725 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_58083_57725_57250 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=477 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_95247_477_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=94850 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_95247_94850_94375 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=476 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_116489_476_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=116281 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_116489_116281_115806 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=476 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_174249_476_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=173889 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_174249_173889_173414 G hg ⟨f,hf⟩

end Signed39.Contraction
