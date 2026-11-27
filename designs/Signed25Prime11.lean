import Signed25Grid11Part0
import Signed25Grid11Part12
import Signed25Grid11Part24
import Signed25Grid11Part36
import Signed25Grid11Part48
import SignedOrbit11Cofactor25
import SignedOrbit11Cofactor25
import Signed539Reduction
import SignedOrbit11Cofactor25
import SignedOrbit11Cofactor25
import Signed25Case869W400
import Signed25Case913W313
import Signed25Case1045W460
import Signed25Case1375W310
import Signed25Case1375W354
import Signed25Case1397W313
import Signed25Case1441W289
import Signed25Case1925W289
import Signed25Case1925W300
import Signed25Case2365W280
import Signed25Case2695W285
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_11_25 : divisorGrid 11 25 163 qInputs_11_25 keep_11_25 := by
  intro d
  fin_cases d
  · exact grid11x25Case0
  · exact grid11x25Case1
  · exact grid11x25Case2
  · exact grid11x25Case3
  · exact grid11x25Case4
  · exact grid11x25Case5
  · exact grid11x25Case6
  · exact grid11x25Case7
  · exact grid11x25Case8
  · exact grid11x25Case9
  · exact grid11x25Case10
  · exact grid11x25Case11
  · exact grid11x25Case12
  · exact grid11x25Case13
  · exact grid11x25Case14
  · exact grid11x25Case15
  · exact grid11x25Case16
  · exact grid11x25Case17
  · exact grid11x25Case18
  · exact grid11x25Case19
  · exact grid11x25Case20
  · exact grid11x25Case21
  · exact grid11x25Case22
  · exact grid11x25Case23
  · exact grid11x25Case24
  · exact grid11x25Case25
  · exact grid11x25Case26
  · exact grid11x25Case27
  · exact grid11x25Case28
  · exact grid11x25Case29
  · exact grid11x25Case30
  · exact grid11x25Case31
  · exact grid11x25Case32
  · exact grid11x25Case33
  · exact grid11x25Case34
  · exact grid11x25Case35
  · exact grid11x25Case36
  · exact grid11x25Case37
  · exact grid11x25Case38
  · exact grid11x25Case39
  · exact grid11x25Case40
  · exact grid11x25Case41
  · exact grid11x25Case42
  · exact grid11x25Case43
  · exact grid11x25Case44
  · exact grid11x25Case45
  · exact grid11x25Case46
  · exact grid11x25Case47
  · exact grid11x25Case48
  · exact grid11x25Case49



private theorem frontier_mixed_275_274_neg1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=275) : ¬∃ f : G → ℤ, IsSDS 274 (-1) f :=
  abelian_short_linear G 11 25 15 1 1 0 274 (-1) 25 0 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_385_345_70 : List RowType := [(0,0),(0,22),(1,17),(2,24),(3,21),(4,30),(5,29),(6,18),(7,19),(8,32),(9,13),(10,28),(11,33),(12,28),(14,32),(15,19),(16,18),(17,29),(18,30),(19,21),(26,30)]
private def stage_0_frontier_mixed_385_345_70 : Stage := [
  ((0,0),⟨⟨3168,(-44),(-90),1⟩,[165,0,0,132,0,0,0,0,0,0,0],0⟩),
  ((0,22),⟨⟨1518,(-44),(-35),1⟩,[0,0,0,22,0,0,0,0,0,0,0],0⟩),
  ((1,17),⟨⟨6930,(-917),0,23⟩,[0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((2,24),⟨⟨19030000,(-1595000),(-210000),39000⟩,[0,0,0,220000,0,0,0,0,0,0,0],1089⟩),
  ((3,21),⟨⟨1834140,(-105105),(-37415),2334⟩,[120120,0,0,62370,0,0,0,0,0,0,0],146⟩),
  ((4,30),⟨⟨1518,(-44),(-35),1⟩,[0,0,0,22,0,0,0,0,0,0,0],0⟩),
  ((5,29),⟨⟨1518,(-44),(-35),1⟩,[0,0,0,22,0,0,0,0,0,0,0],0⟩),
  ((6,18),⟨⟨83160,(-4235),(-2835),(-62)⟩,[0,0,0,0,0,0,0,0,6930,0,0],53⟩),
  ((7,19),⟨⟨312620,(-16170),(-8330),392⟩,[0,0,0,10780,0,0,0,0,0,0,43120],43⟩),
  ((9,13),⟨⟨107800,(-2695),(-2940),73⟩,[2310,0,0,0,0,0,0,3080,0,0,0],3⟩),
  ((11,33),⟨⟨0,(-385),0,11⟩,[0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((12,28),⟨⟨25410,(-9625),(-1120),131⟩,[0,0,0,3080,5390,0,0,0,5390,0,0],54⟩),
  ((14,32),⟨⟨549780,(-5390),(-17885),49⟩,[0,0,0,0,0,0,0,5390,0,0,0],29⟩),
  ((15,19),⟨⟨2775850,(-48125),(-126175),(-850)⟩,[0,0,0,2102100,0,0,0,0,0,0,0],1031⟩),
  ((16,18),⟨⟨315000,0,(-17500),103⟩,[70000,0,0,0,25000,0,0,0,0,0,50000],103⟩),
  ((17,29),⟨⟨288491720,(-3646665),(-10240130),136290⟩,[0,0,0,0,0,0,0,0,3241480,0,0],29468⟩),
  ((18,30),⟨⟨78320,(-990),(-2780),37⟩,[0,0,0,0,0,0,0,0,880,0,0],8⟩),
  ((19,21),⟨⟨630000,0,(-35000),197⟩,[140000,0,0,0,50000,0,0,0,0,0,100000],197⟩),
  ((26,30),⟨⟨900900,(-120505),(-40950),6637⟩,[0,0,0,0,0,0,70840,0,445060,0,0],477⟩)]
private theorem frontier_mixed_385_345_70 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=385) : ¬∃ f : G → ℤ, IsSDS 345 70 f :=
  abelian_short_mixed G 11 35 15 1 1 0 345 70 25 15 2 9 16 5
    types_frontier_mixed_385_345_70 [stage_0_frontier_mixed_385_345_70] ⟨⟨10,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_539_534_259 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=539) : ¬∃ f : G → ℤ, IsSDS 534 259 f :=
  abelian_short_linear G 11 49 15 1 1 0 534 259 25 34 2 9
    ⟨⟨32879,0,(-720),1⟩,[0,0,0,385,0,0,0,0,781,0,0],0⟩ hG (by decide +kernel)



private theorem frontier_mixed_913_852_577 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=913) : ¬∃ f : G → ℤ, IsSDS 852 577 f :=
  abelian_short_linear G 11 83 15 1 1 0 852 577 25 66 2 9
    ⟨⟨3364,0,0,(-1)⟩,[0,0,0,0,0,236,357,480,0,0,0],0⟩ hG (by decide +kernel)


private def types_frontier_mixed_1045_625_350 : List RowType := [(40,40),(41,61),(42,54),(43,63),(44,44),(45,63),(46,54),(47,61),(48,62),(49,57),(50,68),(51,51),(52,72),(53,65),(54,74),(55,55),(56,74),(57,65),(58,72),(59,73),(60,68),(61,79),(62,62),(63,83),(65,85),(66,66),(67,85),(68,76),(70,84)]
private def stage_0_frontier_mixed_1045_625_350 : Stage := [
  ((40,40),⟨⟨0,0,41572,(-981)⟩,[101365,0,485089,0,0,0,0,0,0,0,0],62⟩),
  ((41,61),⟨⟨(-9405000),0,350455,(-3799)⟩,[156750,0,0,0,0,0,0,0,0,0,0],111⟩),
  ((42,54),⟨⟨(-813340),0,2596,0⟩,[0,56298,0,0,0,0,0,0,0,0,25080],43⟩),
  ((45,63),⟨⟨(-8971325),0,285475,(-2950)⟩,[36575,0,0,0,0,0,0,0,0,0,0],223⟩),
  ((46,54),⟨⟨40347450,(-1669720),127300,13914⟩,[0,0,0,0,0,0,0,1544130,0,0,0],99⟩),
  ((47,61),⟨⟨41037150,(-1653570),95475,14133⟩,[0,0,0,0,0,0,0,1508220,0,0,0],77⟩),
  ((48,62),⟨⟨41037150,(-1653570),95475,14133⟩,[0,0,0,0,0,0,0,1508220,0,0,0],77⟩),
  ((49,57),⟨⟨40347450,(-1669720),127300,13914⟩,[0,0,0,0,0,0,0,1544130,0,0,0],99⟩),
  ((50,68),⟨⟨(-8971325),0,285475,(-2950)⟩,[36575,0,0,0,0,0,0,0,0,0,0],223⟩),
  ((53,65),⟨⟨(-813340),0,2596,0⟩,[0,56298,0,0,0,0,0,0,0,0,25080],43⟩),
  ((54,74),⟨⟨(-9405000),0,350455,(-3799)⟩,[156750,0,0,0,0,0,0,0,0,0,0],111⟩),
  ((55,55),⟨⟨(-336490),0,12426,(-188)⟩,[81510,0,139612,0,0,0,0,0,0,0,0],15⟩),
  ((56,74),⟨⟨(-18150),0,890,(-14)⟩,[6600,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((57,65),⟨⟨949870800,(-44415255),6596325,351804⟩,[65963250,0,0,0,0,0,0,0,0,0,0],2680⟩),
  ((60,68),⟨⟨(-29578725),0,508250,(-3425)⟩,[0,0,7670300,0,0,0,0,2743125,0,0,0],908⟩),
  ((62,62),⟨⟨(-3249950),0,0,792⟩,[0,0,0,0,0,0,0,0,0,0,0],103⟩),
  ((63,83),⟨⟨(-27363534),0,399988,18⟩,[0,0,648736,0,0,0,0,2047364,0,0,0],433⟩),
  ((66,66),⟨⟨0,(-15038),10614,0⟩,[0,0,0,0,0,0,0,113512,23466,0,0],21⟩),
  ((67,85),⟨⟨(-193914),0,0,18⟩,[0,0,0,0,0,0,0,0,0,0,0],13⟩),
  ((70,84),⟨⟨(-13365550),0,648375,(-8750)⟩,[0,0,0,0,0,0,0,1280125,0,0,0],359⟩)]
private theorem frontier_mixed_1045_625_350 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1045) : ¬∃ f : G → ℤ, IsSDS 625 350 f :=
  abelian_short_mixed G 11 95 15 0 1 0 625 350 25 55 2 9 26 3
    types_frontier_mixed_1045_625_350 [stage_0_frontier_mixed_1045_625_350] ⟨⟨3212,(-132),15,1⟩,[0,0,0,0,0,0,0,154,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1177_408_133 : List RowType := [(21,29),(22,22),(23,29),(28,32),(29,35),(30,30),(31,39),(32,40),(33,33),(34,40),(35,39),(39,43),(40,46),(41,41),(42,50),(43,51),(44,44),(45,51),(46,50),(50,54),(51,57)]
private def stage_0_frontier_mixed_1177_408_133 : Stage := [
  ((22,22),⟨⟨(-1260567),0,0,407⟩,[0,0,0,0,0,0,0,0,0,0,0],36⟩),
  ((23,29),⟨⟨0,0,0,(-5335)⟩,[0,3140236,0,0,0,0,2235123,0,0,0,0],882⟩),
  ((28,32),⟨⟨(-713262),0,22684,(-179)⟩,[0,0,0,0,0,0,0,20009,0,0,0],11⟩),
  ((30,30),⟨⟨(-23403468),0,716579,(-6081)⟩,[0,0,0,0,0,0,0,0,5661370,0,0],379⟩),
  ((31,39),⟨⟨(-14427666),0,425539,(-4197)⟩,[0,0,0,0,0,0,0,0,4251324,0,0],346⟩),
  ((32,40),⟨⟨(-1260567),0,0,(-913)⟩,[0,0,0,0,0,0,0,0,0,0,0],216⟩),
  ((34,40),⟨⟨(-1320594),0,61525,(-861)⟩,[98868,0,0,0,0,0,0,0,0,0,0],23⟩),
  ((41,41),⟨⟨(-6281649),0,0,209⟩,[0,2006785,4312528,0,0,0,0,0,0,0,0],378⟩),
  ((44,44),⟨⟨(-184789),0,0,(-11)⟩,[0,0,0,0,0,0,81213,0,0,0,0],20⟩),
  ((45,51),⟨⟨(-148302),0,5243,(-71)⟩,[0,0,0,0,0,0,0,0,28248,0,0],4⟩),
  ((50,54),⟨⟨(-223630),0,11877,(-221)⟩,[0,0,0,0,0,0,0,0,0,0,0],9⟩),
  ((51,57),⟨⟨1993838,(-191316),52430,2066⟩,[0,0,0,0,0,0,20758,0,60562,0,0],11⟩)]
private theorem frontier_mixed_1177_408_133 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1177) : ¬∃ f : G → ℤ, IsSDS 408 133 f :=
  abelian_short_mixed G 11 107 15 0 1 0 408 133 25 36 2 9 39 4
    types_frontier_mixed_1177_408_133 [stage_0_frontier_mixed_1177_408_133] ⟨⟨(-4032),(-27),189,(-2)⟩,[864,0,56,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1177_793_518 : List RowType := [(56,62),(57,61),(61,65),(62,68),(63,63),(64,72),(65,73),(66,66),(67,73),(68,72),(72,76),(73,79),(74,74),(75,83),(76,84),(77,77),(78,84),(85,85)]
private def stage_0_frontier_mixed_1177_793_518 : Stage := [
  ((56,62),⟨⟨26411880,(-938069),181579,5200⟩,[0,0,0,0,0,0,0,0,0,0,0],57⟩),
  ((61,65),⟨⟨(-18008100),0,370113,(-2469)⟩,[3811126,0,0,0,0,0,0,0,0,0,0],289⟩),
  ((62,68),⟨⟨(-400180),0,8988,(-62)⟩,[42372,0,0,0,0,0,0,0,0,0,0],5⟩),
  ((64,72),⟨⟨1590127,0,0,(-847)⟩,[0,0,0,0,0,0,282480,0,0,123585,0],228⟩),
  ((73,79),⟨⟨79394,0,0,(-29)⟩,[0,0,0,0,0,0,0,0,51360,0,0],5⟩),
  ((74,74),⟨⟨(-12553882),0,133215,163⟩,[0,0,0,0,0,0,1106380,0,0,0,0],207⟩),
  ((76,84),⟨⟨(-21805102),0,600163,(-5389)⟩,[5889708,0,0,0,0,0,0,0,0,0,0],482⟩),
  ((77,77),⟨⟨(-37254404),0,1282395,(-12601)⟩,[10162218,0,0,0,0,0,0,0,0,0,0],675⟩),
  ((78,84),⟨⟨0,0,0,(-96)⟩,[0,0,0,0,0,0,222774,0,0,0,78966],49⟩),
  ((85,85),⟨⟨0,0,(-3036),0⟩,[0,115302,85096,0,0,0,0,0,0,0,0],13⟩)]
private theorem frontier_mixed_1177_793_518 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1177) : ¬∃ f : G → ℤ, IsSDS 793 518 f :=
  abelian_short_mixed G 11 107 15 0 1 0 793 518 25 71 2 9 39 4
    types_frontier_mixed_1177_793_518 [stage_0_frontier_mixed_1177_793_518] ⟨⟨0,0,66,(-1)⟩,[0,0,0,0,0,0,168,0,0,147,0],0⟩ hG (by decide +kernel)



private def types_frontier_mixed_1375_1069_794 : List RowType := [(80,82),(80,104),(81,81),(81,103),(82,86),(83,97),(84,92),(85,93),(86,100),(87,91),(88,88),(88,110),(89,91),(89,113),(90,100),(91,93),(91,115),(92,92),(92,114),(93,97),(94,108),(95,103),(96,104),(99,99),(99,121),(101,111),(102,104),(103,103),(104,108),(105,119)]
private def stage_0_frontier_mixed_1375_1069_794 : Stage := [
  ((80,82),⟨⟨(-10120000),0,110000,(-275)⟩,[0,0,0,0,0,0,0,0,0,0,0],184⟩),
  ((81,81),⟨⟨0,(-286154),245410,0⟩,[0,0,0,0,1122594,1644038,0,0,0,0,0],289⟩),
  ((81,103),⟨⟨0,0,1506875,(-18633)⟩,[0,0,0,0,6429500,9385750,0,3767500,0,0,0],1392⟩),
  ((82,86),⟨⟨8002500,(-170500),0,902⟩,[0,0,0,0,33000,0,0,0,0,0,0],3⟩),
  ((83,97),⟨⟨28336,(-594),10,3⟩,[77,0,0,0,0,0,0,0,0,0,0],0⟩),
  ((86,100),⟨⟨70573800,(-1517725),15000,7943⟩,[0,0,0,0,313500,0,0,0,0,0,0],13⟩),
  ((87,91),⟨⟨(-1588250),0,0,104⟩,[0,3750,2250,0,4500,0,0,4500,0,2250,0],51⟩),
  ((88,88),⟨⟨0,0,(-12650),0⟩,[0,0,0,0,0,418088,1087482,0,0,0,0],103⟩),
  ((92,114),⟨⟨3187500,0,0,(-472)⟩,[0,0,0,0,0,0,0,15750,0,0,0],47⟩),
  ((93,97),⟨⟨0,(-2530),0,0⟩,[57706,0,0,14014,120384,0,0,0,0,0,0],21⟩),
  ((94,108),⟨⟨108707500,(-2414500),151875,11611⟩,[390500,0,0,605000,0,0,0,0,0,0,0],36⟩),
  ((95,103),⟨⟨0,(-2550),1975,0⟩,[0,0,0,0,20175,0,0,0,0,0,0],4⟩),
  ((96,104),⟨⟨0,(-190000),0,0⟩,[0,9650000,0,6200000,0,0,0,0,0,0,0],1577⟩),
  ((99,99),⟨⟨0,0,(-6897),0⟩,[0,0,0,0,0,0,459657,226116,0,0,0],52⟩),
  ((99,121),⟨⟨0,(-334037),277981,0⟩,[1923768,0,0,0,0,665544,0,1000450,550462,0,0],189⟩),
  ((101,111),⟨⟨0,160875,0,(-2409)⟩,[0,3841750,0,0,0,0,0,0,0,0,0],676⟩),
  ((103,103),⟨⟨0,0,(-2200),0⟩,[0,0,0,0,0,0,0,0,0,0,0],7⟩),
  ((105,119),⟨⟨0,41250,0,(-550)⟩,[0,0,0,385000,0,123750,0,0,0,0,0],63⟩)]
private theorem frontier_mixed_1375_1069_794 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1375) : ¬∃ f : G → ℤ, IsSDS 1069 794 f :=
  abelian_short_mixed G 11 125 15 1 1 0 1069 794 25 95 2 9 91 8
    types_frontier_mixed_1375_1069_794 [stage_0_frontier_mixed_1375_1069_794] ⟨⟨9270,(-193),0,1⟩,[0,0,0,12,22,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1375_1245_970 : List RowType := [(90,100),(90,122),(91,93),(91,115),(92,92),(92,114),(93,97),(93,119),(94,108),(95,103),(96,104),(99,99),(99,121),(101,111),(102,104),(103,103),(104,108),(105,119),(112,122)]
private def stage_0_frontier_mixed_1375_1245_970 : Stage := [
  ((92,92),⟨⟨(-25806),0,0,0⟩,[0,0,2706,0,0,0,0,0,0,0,0],1⟩),
  ((92,114),⟨⟨(-28314),0,0,0⟩,[0,0,5214,2508,0,0,0,0,0,0,0],1⟩),
  ((93,119),⟨⟨1108250,0,0,(-242)⟩,[0,0,0,0,0,0,459250,0,0,0,0],87⟩),
  ((94,108),⟨⟨0,0,0,(-2871)⟩,[0,0,0,2029500,0,0,0,8064375,0,0,0],2704⟩),
  ((95,103),⟨⟨0,0,0,(-6325)⟩,[0,0,0,0,0,0,14492500,0,0,0,0],6272⟩),
  ((96,104),⟨⟨(-13794),0,0,0⟩,[0,0,1144,0,0,0,0,0,0,0,0],1⟩),
  ((103,103),⟨⟨0,0,(-24511569),0⟩,[0,0,0,0,0,0,0,0,0,0,0],105616⟩),
  ((112,122),⟨⟨0,0,0,(-104)⟩,[0,0,777500,0,0,0,0,0,0,0,0],99⟩)]
private theorem frontier_mixed_1375_1245_970 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1375) : ¬∃ f : G → ℤ, IsSDS 1245 970 f :=
  abelian_short_mixed G 11 125 15 1 1 0 1245 970 25 105 2 9 91 8
    types_frontier_mixed_1375_1245_970 [stage_0_frontier_mixed_1375_1245_970] ⟨⟨30492,0,207,(-5)⟩,[0,0,0,0,0,1232,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_1397_1248_973 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1397) : ¬∃ f : G → ℤ, IsSDS 1248 973 f :=
  abelian_short_linear G 11 127 15 1 1 0 1248 973 25 106 2 9
    ⟨⟨66132,0,1015,(-17)⟩,[0,0,0,0,0,0,14718,3080,0,0,0],0⟩ hG (by decide +kernel)




private theorem frontier_mixed_1925_1785_1510 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1925) : ¬∃ f : G → ℤ, IsSDS 1785 1510 f :=
  abelian_short_linear G 11 175 15 1 1 0 1785 1510 25 155 2 9
    ⟨⟨153,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1925_1884_1609 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1925) : ¬∃ f : G → ℤ, IsSDS 1884 1609 f :=
  abelian_short_linear G 11 175 15 1 1 0 1884 1609 25 160 2 9
    ⟨⟨26775,(-328),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)



private theorem frontier_mixed_2695_2650_2375 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2695) : ¬∃ f : G → ℤ, IsSDS 2650 2375 f :=
  abelian_short_linear G 11 245 15 1 1 0 2650 2375 25 230 2 9
    ⟨⟨55860,(-473),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6875_282_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6875) : ¬∃ f : G → ℤ, IsSDS 282 7 f :=
  abelian_short_linear G 11 625 15 2 1 0 282 7 25 20 2 9
    ⟨⟨(-2192),0,38,1⟩,[0,0,0,0,0,761,332,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6875_6717_6442 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6875) : ¬∃ f : G → ℤ, IsSDS 6717 6442 f :=
  abelian_short_linear G 11 625 15 1 1 0 6717 6442 25 605 2 9
    ⟨⟨595,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8327_282_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8327) : ¬∃ f : G → ℤ, IsSDS 282 7 f :=
  abelian_short_linear G 11 757 15 1 1 0 282 7 25 22 2 9
    ⟨⟨(-32714),0,295,21⟩,[110,0,0,0,0,0,0,1188,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8327_8125_7850 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8327) : ¬∃ f : G → ℤ, IsSDS 8125 7850 f :=
  abelian_short_linear G 11 757 15 1 1 0 8125 7850 25 735 2 9
    ⟨⟨727,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9625_280_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9625) : ¬∃ f : G → ℤ, IsSDS 280 5 f :=
  abelian_short_linear G 11 875 15 2 1 0 280 5 25 20 2 9
    ⟨⟨(-77),0,2,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9625_9465_9190 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9625) : ¬∃ f : G → ℤ, IsSDS 9465 9190 f :=
  abelian_short_linear G 11 875 15 1 1 0 9465 9190 25 855 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10087_277_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10087) : ¬∃ f : G → ℤ, IsSDS 277 2 f :=
  abelian_short_linear G 11 917 15 6 1 0 277 2 25 13 2 9
    ⟨⟨0,(-11429),1950,167⟩,[0,0,0,0,0,0,0,0,0,1584,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10087_10078_9803 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10087) : ¬∃ f : G → ℤ, IsSDS 10078 9803 f :=
  abelian_short_linear G 11 917 15 1 1 0 10078 9803 25 904 2 9
    ⟨⟨(-917),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11825_276_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11825) : ¬∃ f : G → ℤ, IsSDS 276 1 f :=
  abelian_short_linear G 11 1075 15 7 1 0 276 1 25 10 2 9
    ⟨⟨0,(-110),25,1⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13475_277_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13475) : ¬∃ f : G → ℤ, IsSDS 277 2 f :=
  abelian_short_linear G 11 1225 15 5 1 0 277 2 25 15 2 9
    ⟨⟨0,(-1592100),192815,33054⟩,[0,0,0,0,826350,1156890,264432,0,0,0,1432340],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13475_13422_13147 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13475) : ¬∃ f : G → ℤ, IsSDS 13422 13147 f :=
  abelian_short_linear G 11 1225 15 1 1 0 13422 13147 25 1210 2 9
    ⟨⟨(-1225),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_17149_276_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=17149) : ¬∃ f : G → ℤ, IsSDS 276 1 f :=
  abelian_short_linear G 11 1559 15 6 1 0 276 1 25 12 2 9
    ⟨⟨0,(-974),175,9⟩,[0,0,0,0,0,0,0,252,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_17347_277_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=17347) : ¬∃ f : G → ℤ, IsSDS 277 2 f :=
  abelian_short_linear G 11 1577 15 4 1 0 277 2 25 17 2 9
    ⟨⟨0,0,28661022,(-15093141)⟩,[0,0,0,0,443986088,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_17347_17250_16975 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=17347) : ¬∃ f : G → ℤ, IsSDS 17250 16975 f :=
  abelian_short_linear G 11 1577 15 1 1 0 17250 16975 25 1560 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23441_276_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23441) : ¬∃ f : G → ℤ, IsSDS 276 1 f :=
  abelian_short_linear G 11 2131 15 5 1 0 276 1 25 14 2 9
    ⟨⟨0,(-103),15,1⟩,[0,0,0,15,36,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23441_23409_23134 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23441) : ¬∃ f : G → ℤ, IsSDS 23409 23134 f :=
  abelian_short_linear G 11 2131 15 1 1 0 23409 23134 25 2117 2 9
    ⟨⟨(-2131),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_26543_277_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=26543) : ¬∃ f : G → ℤ, IsSDS 277 2 f :=
  abelian_short_linear G 11 2413 15 2 1 0 277 2 25 21 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_26543_26358_26083 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=26543) : ¬∃ f : G → ℤ, IsSDS 26358 26083 f :=
  abelian_short_linear G 11 2413 15 1 1 0 26358 26083 25 2392 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_30701_276_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=30701) : ¬∃ f : G → ℤ, IsSDS 276 1 f :=
  abelian_short_linear G 11 2791 15 4 1 0 276 1 25 16 2 9
    ⟨⟨0,0,18674,(-7043)⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_30701_30625_30350 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=30701) : ¬∃ f : G → ℤ, IsSDS 30625 30350 f :=
  abelian_short_linear G 11 2791 15 1 1 0 30625 30350 25 2775 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_38929_276_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=38929) : ¬∃ f : G → ℤ, IsSDS 276 1 f :=
  abelian_short_linear G 11 3539 15 3 1 0 276 1 25 18 2 9
    ⟨⟨0,0,0,(-1)⟩,[0,0,0,9,16,25,36,49,64,81,100],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_38929_38809_38534 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=38929) : ¬∃ f : G → ℤ, IsSDS 38809 38534 f :=
  abelian_short_linear G 11 3539 15 1 1 0 38809 38534 25 3521 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_48125_276_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=48125) : ¬∃ f : G → ℤ, IsSDS 276 1 f :=
  abelian_short_linear G 11 4375 15 2 1 0 276 1 25 20 2 9
    ⟨⟨6,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_48125_47961_47686 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=48125) : ¬∃ f : G → ℤ, IsSDS 47961 47686 f :=
  abelian_short_linear G 11 4375 15 1 1 0 47961 47686 25 4355 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_58289_276_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=58289) : ¬∃ f : G → ℤ, IsSDS 276 1 f :=
  abelian_short_linear G 11 5299 15 1 1 0 276 1 25 22 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_58289_58081_57806 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=58289) : ¬∃ f : G → ℤ, IsSDS 58081 57806 f :=
  abelian_short_linear G 11 5299 15 1 1 0 58081 57806 25 5277 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_69421_276_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=69421) : ¬∃ f : G → ℤ, IsSDS 276 1 f :=
  abelian_short_linear G 11 6311 15 0 1 0 276 1 25 24 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_69421_69169_68894 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=69421) : ¬∃ f : G → ℤ, IsSDS 69169 68894 f :=
  abelian_short_linear G 11 6311 15 0 1 0 69169 68894 25 6287 2 9
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_11_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=11*m)
    (hm : 11 < m) (hn : k-l=(11:ℤ)*25) : False := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_11_25
  simp only [keep_11_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=274 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_275_274_neg1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=345 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_385_345_70 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=300 := by omega
    rw [hk,hL] at hf
    exact Signed39.Shape.no_473_300_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=325 := by omega
    rw [hk,hL] at hf
    exact reduced_539_325 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=534 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_539_534_259 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=400 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_869_400_125 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=609 := by omega
    rw [hk,hL] at hf
    exact Signed39.Shape.no_869_609_334 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=313 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_913_313_38 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=852 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_913_852_577 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=460 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1045_460_185 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1045_625_350 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=408 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1177_408_133 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=793 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1177_793_518 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=277 := by omega
    rw [hk,hL] at hf
    exact Signed39.Shape.no_1375_277_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=310 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1375_310_35 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=354 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1375_354_79 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1069 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1375_1069_794 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1245 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1375_1245_970 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=313 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1397_313_38 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1248 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1397_1248_973 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=289 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1441_289_14 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=276 := by omega
    rw [hk,hL] at hf
    exact Signed39.Shape.no_1661_276_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=289 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1925_289_14 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=300 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1925_300_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1785 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1925_1785_1510 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1884 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1925_1884_1609 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=280 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2365_280_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=285 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2695_285_10 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2650 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2695_2650_2375 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=282 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6875_282_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6717 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6875_6717_6442 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=282 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8327_282_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=8125 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8327_8125_7850 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=280 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9625_280_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=9465 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9625_9465_9190 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=277 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10087_277_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=10078 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10087_10078_9803 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=276 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11825_276_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=277 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13475_277_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=13422 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13475_13422_13147 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=276 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_17149_276_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=277 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_17347_277_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=17250 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_17347_17250_16975 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=276 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23441_276_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=23409 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23441_23409_23134 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=277 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_26543_277_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=26358 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_26543_26358_26083 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=276 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_30701_276_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=30625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_30701_30625_30350 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=276 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_38929_276_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=38809 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_38929_38809_38534 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=276 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_48125_276_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=47961 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_48125_47961_47686 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=276 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_58289_276_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=58081 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_58289_58081_57806 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=276 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_69421_276_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=69169 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_69421_69169_68894 G hg ⟨f,hf⟩

end Signed39.Contraction
