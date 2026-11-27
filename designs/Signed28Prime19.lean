import Signed28Grid19Part0
import Signed28Grid19Part12
import Signed28Grid19Part24
import Signed28Grid19Part36
import Signed28Grid19Part48
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_19_28 : divisorGrid 19 28 240 qInputs_19_28 keep_19_28 := by
  intro d
  fin_cases d
  · exact grid19x28Case0
  · exact grid19x28Case1
  · exact grid19x28Case2
  · exact grid19x28Case3
  · exact grid19x28Case4
  · exact grid19x28Case5
  · exact grid19x28Case6
  · exact grid19x28Case7
  · exact grid19x28Case8
  · exact grid19x28Case9
  · exact grid19x28Case10
  · exact grid19x28Case11
  · exact grid19x28Case12
  · exact grid19x28Case13
  · exact grid19x28Case14
  · exact grid19x28Case15
  · exact grid19x28Case16
  · exact grid19x28Case17
  · exact grid19x28Case18
  · exact grid19x28Case19
  · exact grid19x28Case20
  · exact grid19x28Case21
  · exact grid19x28Case22
  · exact grid19x28Case23
  · exact grid19x28Case24
  · exact grid19x28Case25
  · exact grid19x28Case26
  · exact grid19x28Case27
  · exact grid19x28Case28
  · exact grid19x28Case29
  · exact grid19x28Case30
  · exact grid19x28Case31
  · exact grid19x28Case32
  · exact grid19x28Case33
  · exact grid19x28Case34
  · exact grid19x28Case35
  · exact grid19x28Case36
  · exact grid19x28Case37
  · exact grid19x28Case38
  · exact grid19x28Case39
  · exact grid19x28Case40
  · exact grid19x28Case41
  · exact grid19x28Case42
  · exact grid19x28Case43
  · exact grid19x28Case44
  · exact grid19x28Case45
  · exact grid19x28Case46
  · exact grid19x28Case47
  · exact grid19x28Case48
  · exact grid19x28Case49
  · exact grid19x28Case50
  · exact grid19x28Case51
  · exact grid19x28Case52
  · exact grid19x28Case53
  · exact grid19x28Case54
  · exact grid19x28Case55



private theorem frontier_mixed_1121_784_252 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1121) : ¬∃ f : G → ℤ, IsSDS 784 252 f :=
  abelian_short_linear G 19 59 22 1 2 9 784 252 28 28 18 53
    ⟨⟨484,0,0,(-1)⟩,[0,0,0,0,0,0,0,192,0,300,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1121_841_309 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1121) : ¬∃ f : G → ℤ, IsSDS 841 309 f :=
  abelian_short_linear G 19 59 22 1 2 9 841 309 28 31 18 53
    ⟨⟨2658765,(-485108),117840,6384⟩,[0,0,0,0,0,0,1119480,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1539_819_287 : List RowType := [(13,49),(15,45),(17,35),(17,73),(19,57),(21,35),(21,73),(23,45),(25,49),(27,47),(29,39),(29,77),(31,63),(33,43),(35,55),(37,61),(39,61),(41,55),(43,43),(47,77),(55,73)]
private def stage_0_frontier_mixed_1539_819_287 : Stage := [
  ((13,49),⟨⟨(-346275),0,0,19⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,147744,0,0,0,86184],40⟩),
  ((15,45),⟨⟨(-722475),0,18756,(-297)⟩,[0,0,0,53352,0,0,0,0,57456,0,0,0,0,0,42408,0,0,0,0],16⟩),
  ((19,57),⟨⟨(-1100385),0,0,(-247)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],68⟩),
  ((21,73),⟨⟨(-1591839),0,36450,(-963)⟩,[0,119016,0,0,0,0,0,0,580716,0,0,0,0,0,0,0,0,98496,190836],58⟩),
  ((27,47),⟨⟨(-9598743),0,393660,(-9477)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,2991816,0,0,0,0],368⟩),
  ((29,39),⟨⟨(-93195),0,2700,(-65)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12312,0,0],4⟩),
  ((29,77),⟨⟨(-1181439),0,33858,(-779)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,135432,0,0],46⟩),
  ((31,63),⟨⟨(-124659),0,0,19⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((33,43),⟨⟨(-1751895),0,49140,(-765)⟩,[0,0,0,86184,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],56⟩),
  ((35,55),⟨⟨(-747441),0,15147,(-130)⟩,[0,0,0,0,0,0,0,0,0,0,196992,0,0,0,0,0,0,0,0],23⟩),
  ((37,61),⟨⟨(-2004291),0,59940,(-1481)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],220⟩),
  ((39,61),⟨⟨(-1546695),0,33048,(-9)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],32⟩),
  ((41,55),⟨⟨0,0,(-9045),175⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,7182,0,0,0,0],43⟩),
  ((43,43),⟨⟨(-841035),0,0,475⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],28⟩),
  ((47,77),⟨⟨(-1805247),0,36126,(-427)⟩,[0,0,0,0,0,0,0,0,0,0,307800,0,0,0,0,0,0,0,0],62⟩)]
private theorem frontier_mixed_1539_819_287 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1539) : ¬∃ f : G → ℤ, IsSDS 819 287 f :=
  abelian_short_mixed G 19 81 22 1 2 9 819 287 28 35 18 53 64 15
    types_frontier_mixed_1539_819_287 [stage_0_frontier_mixed_1539_819_287] ⟨⟨(-196),(-19),17,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1539_1028_496 : List RowType := [(24,62),(26,44),(28,58),(30,66),(32,68),(34,64),(36,54),(38,38),(38,76),(40,54),(42,64),(44,68),(48,58),(52,62)]
private def stage_0_frontier_mixed_1539_1028_496 : Stage := [
  ((24,62),⟨⟨0,0,0,(-1197)⟩,[0,0,0,0,0,0,0,240084,0,369360,0,0,0,0,2142288,0,0,0,0],128⟩),
  ((28,58),⟨⟨0,0,2790,(-311)⟩,[0,0,188100,0,0,0,0,0,0,0,366624,0,0,0,0,0,0,0,0],22⟩),
  ((36,54),⟨⟨0,0,0,(-162)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,204120,0,0,209952,0],19⟩),
  ((40,54),⟨⟨0,0,0,(-7733)⟩,[10138932,0,0,0,0,0,0,0,0,1181952,14811336,0,0,0,0,0,0,0,0],676⟩),
  ((42,64),⟨⟨55404,0,0,(-171)⟩,[129276,0,0,0,0,0,55404,0,0,0,166212,0,0,0,0,0,0,0,0],14⟩),
  ((44,68),⟨⟨0,0,0,(-95)⟩,[9234,0,0,0,0,0,0,0,0,0,0,27702,0,0,0,70794,0,0,0],13⟩),
  ((48,58),⟨⟨0,(-3933),0,0⟩,[0,0,99522,0,5130,0,0,0,0,0,0,0,0,0,0,0,0,0,0],13⟩),
  ((52,62),⟨⟨0,0,0,(-437)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43092,0,0,0],64⟩)]
private theorem frontier_mixed_1539_1028_496 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1539) : ¬∃ f : G → ℤ, IsSDS 1028 496 f :=
  abelian_short_mixed G 19 81 22 1 2 9 1028 496 28 46 18 53 64 15
    types_frontier_mixed_1539_1028_496 [stage_0_frontier_mixed_1539_1028_496] ⟨⟨38,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1767_584_52 : List RowType := [((-6),58),((-4),30),((-4),68),((-2),36),((-2),74),(0,0),(0,38),(0,76),(2,36),(2,74),(4,30),(4,68),(6,58),(8,44),(8,82),(10,26),(10,64),(12,42),(12,80),(14,54),(14,92),(16,62),(18,28),(18,66),(20,66),(22,24),(22,62),(24,54),(24,92),(26,42),(26,80),(28,64),(30,44),(30,82),(32,58),(34,68),(36,74),(38,38),(38,76)]
private def stage_0_frontier_mixed_1767_584_52 : Stage := [
  (((-4),68),⟨⟨0,(-480624),0,16853⟩,[0,0,0,0,0,0,0,0,0,0,1519620,0,0,0,0,0,0,0,1802340],140⟩),
  ((0,38),⟨⟨9120,(-1558),60,49⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1368],0⟩),
  ((0,76),⟨⟨3385500,(-577792),22200,18300⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,507825],0⟩),
  ((4,30),⟨⟨0,(-183179),0,6308⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,212040],105⟩),
  ((4,68),⟨⟨0,(-183179),0,6308⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,212040],105⟩),
  ((6,58),⟨⟨0,(-2385450),174096,73197⟩,[0,0,0,339264,0,0,0,0,0,0,0,0,7718256,0,0,0,0,0,9923472],308⟩),
  ((10,26),⟨⟨0,(-1174466),0,44365⟩,[0,0,0,334552,419368,0,0,0,0,0,0,0,0,0,0,0,0,0,0],312⟩),
  ((10,64),⟨⟨0,(-1174466),0,44365⟩,[0,0,0,334552,419368,0,0,0,0,0,0,0,0,0,0,0,0,0,0],312⟩),
  ((12,42),⟨⟨0,(-590178),30132,17859⟩,[0,0,0,1950768,0,0,0,0,0,0,0,0,1102608,0,0,0,424080,0,1017792],116⟩),
  ((14,54),⟨⟨0,(-56544),7719,1570⟩,[0,0,0,67146,0,0,0,0,0,0,0,0,0,0,0,0,0,0,91884],7⟩),
  ((18,28),⟨⟨0,(-10602),0,171⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((18,66),⟨⟨0,(-10602),0,171⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((20,66),⟨⟨0,(-24738),0,931⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((22,24),⟨⟨0,(-604314),0,14953⟩,[0,0,0,5442360,0,0,0,0,0,0,0,0,42408,0,0,0,0,0,0],352⟩),
  ((22,62),⟨⟨2273540,(-367536),0,11951⟩,[0,0,0,0,0,0,0,0,0,0,0,0,186124,0,0,0,0,0,0],16⟩),
  ((24,92),⟨⟨0,(-38874),3348,1389⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,70680,0,0,0,0],4⟩),
  ((34,68),⟨⟨0,(-24738),0,893⟩,[0,0,0,0,0,0,0,0,0,0,0,0,127224,0,0,0,0,0,0],8⟩),
  ((36,74),⟨⟨(-84816),(-166098),0,5073⟩,[84816,0,0,0,0,0,0,84816,0,183768,0,296856,0,0,0,0,0,0,0],40⟩),
  ((38,38),⟨⟨0,(-3534),0,76⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((38,76),⟨⟨0,(-3534),0,76⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩)]
private theorem frontier_mixed_1767_584_52 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1767) : ¬∃ f : G → ℤ, IsSDS 584 52 f :=
  abelian_short_mixed G 19 93 22 2 2 9 584 52 28 16 18 53 49 10
    types_frontier_mixed_1767_584_52 [stage_0_frontier_mixed_1767_584_52] ⟨⟨0,(-13490),1092,451⟩,[0,0,0,0,0,5016,0,0,31008,0,0,0,9576,0,0,0,32680,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1767_964_432 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1767) : ¬∃ f : G → ℤ, IsSDS 964 432 f :=
  abelian_short_linear G 19 93 22 1 2 9 964 432 28 46 18 53
    ⟨⟨1148684784,(-53737125),1583688,576992⟩,[0,0,0,0,0,0,6878352,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1767_983_451 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1767) : ¬∃ f : G → ℤ, IsSDS 983 451 f :=
  abelian_short_linear G 19 93 22 1 2 9 983 451 28 47 18 53
    ⟨⟨40605565,(-1808040),66612,18240⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1767_1743_1211 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1767) : ¬∃ f : G → ℤ, IsSDS 1743 1211 f :=
  abelian_short_linear G 19 93 22 1 2 9 1743 1211 28 77 18 53
    ⟨⟨6603,(-164),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1957_709_177 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1957) : ¬∃ f : G → ℤ, IsSDS 709 177 f :=
  abelian_short_linear G 19 103 22 2 2 9 709 177 28 31 18 53
    ⟨⟨6707,(-570),96,7⟩,[0,0,0,0,0,0,0,0,0,0,0,0,684,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1957_1488_956 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1957) : ¬∃ f : G → ℤ, IsSDS 1488 956 f :=
  abelian_short_linear G 19 103 22 1 2 9 1488 956 28 72 18 53
    ⟨⟨(-6092),0,138,(-1)⟩,[0,0,0,32,0,0,0,0,0,0,0,0,864,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3363_616_84 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3363) : ¬∃ f : G → ℤ, IsSDS 616 84 f :=
  abelian_short_linear G 19 177 22 2 2 9 616 84 28 28 18 53
    ⟨⟨(-75544),(-418),1760,17⟩,[0,0,0,0,0,0,0,0,14440,0,4104,9424,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3363_635_103 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3363) : ¬∃ f : G → ℤ, IsSDS 635 103 f :=
  abelian_short_linear G 19 177 22 1 2 9 635 103 28 31 18 53
    ⟨⟨0,(-4503),1435,68⟩,[0,0,0,0,152,0,0,0,0,0,0,0,12540,0,18582,0,3990,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3363_2820_2288 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3363) : ¬∃ f : G → ℤ, IsSDS 2820 2288 f :=
  abelian_short_linear G 19 177 22 1 2 9 2820 2288 28 146 18 53
    ⟨⟨0,0,4225,(-36)⟩,[0,0,0,0,0,0,0,0,0,0,0,112746,0,99826,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3363_2915_2383 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3363) : ¬∃ f : G → ℤ, IsSDS 2915 2383 f :=
  abelian_short_linear G 19 177 22 1 2 9 2915 2383 28 149 18 53
    ⟨⟨0,0,133,(-1)⟩,[0,0,0,0,0,0,834,0,0,0,0,0,0,0,0,0,522,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5871_591_59 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5871) : ¬∃ f : G → ℤ, IsSDS 591 59 f :=
  abelian_short_linear G 19 309 22 0 2 9 591 59 28 31 18 53
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5871_5284_4752 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5871) : ¬∃ f : G → ℤ, IsSDS 5284 4752 f :=
  abelian_short_linear G 19 309 22 0 2 9 5284 4752 28 278 18 53
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7277_548_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7277) : ¬∃ f : G → ℤ, IsSDS 548 16 f :=
  abelian_short_linear G 19 383 22 5 2 9 548 16 28 18 18 53
    ⟨⟨0,(-39547189),4660812,1190160⟩,[0,165757596,0,14380796,0,0,0,0,0,0,0,0,0,0,0,0,48440576,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7277_7141_6609 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7277) : ¬∃ f : G → ℤ, IsSDS 7141 6609 f :=
  abelian_short_linear G 19 383 22 1 2 9 7141 6609 28 365 18 53
    ⟨⟨(-383),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10089_560_28 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10089) : ¬∃ f : G → ℤ, IsSDS 560 28 f :=
  abelian_short_linear G 19 531 22 0 2 9 560 28 28 28 18 53
    ⟨⟨(-38),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10089_9585_9053 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10089) : ¬∃ f : G → ℤ, IsSDS 9585 9053 f :=
  abelian_short_linear G 19 531 22 0 2 9 9585 9053 28 503 18 53
    ⟨⟨493,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11533_541_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11533) : ¬∃ f : G → ℤ, IsSDS 541 9 f :=
  abelian_short_linear G 19 607 22 5 2 9 541 9 28 17 18 53
    ⟨⟨(-7695),(-1596),180,47⟩,[0,2584,0,0,0,5320,760,4864,0,0,1672,304,304,3040,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11533_11428_10896 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11533) : ¬∃ f : G → ℤ, IsSDS 11428 10896 f :=
  abelian_short_linear G 19 607 22 1 2 9 11428 10896 28 590 18 53
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20159_535_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20159) : ¬∃ f : G → ℤ, IsSDS 535 3 f :=
  abelian_short_linear G 19 1061 22 7 2 9 535 3 28 13 18 53
    ⟨⟨(-8265),(-1748),260,17⟩,[760,3496,0,4256,0,2280,0,0,0,0,0,0,0,0,0,760,0,2128,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28709_533_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28709) : ¬∃ f : G → ℤ, IsSDS 533 1 f :=
  abelian_short_linear G 19 1511 22 9 2 9 533 1 28 9 18 53
    ⟨⟨(-1494048),(-134945),64938,0⟩,[0,269890,0,0,0,269890,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_34599_535_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=34599) : ¬∃ f : G → ℤ, IsSDS 535 3 f :=
  abelian_short_linear G 19 1821 22 5 2 9 535 3 28 17 18 53
    ⟨⟨0,0,125,(-47)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_34599_34488_33956 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=34599) : ¬∃ f : G → ℤ, IsSDS 34488 33956 f :=
  abelian_short_linear G 19 1821 22 1 2 9 34488 33956 28 1804 18 53
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_60477_533_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=60477) : ¬∃ f : G → ℤ, IsSDS 533 1 f :=
  abelian_short_linear G 19 3183 22 7 2 9 533 1 28 13 18 53
    ⟨⟨0,(-437),35,6⟩,[152,0,266,0,0,0,0,0,0,0,0,266,0,152,0,760,0,760,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_103797_533_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=103797) : ¬∃ f : G → ℤ, IsSDS 533 1 f :=
  abelian_short_linear G 19 5463 22 5 2 9 533 1 28 17 18 53
    ⟨⟨0,0,4055312,(-2973807)⟩,[226000368,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_103797_103684_103152 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=103797) : ¬∃ f : G → ℤ, IsSDS 103684 103152 f :=
  abelian_short_linear G 19 5463 22 1 2 9 103684 103152 28 5446 18 53
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_19_28_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=19*m)
    (hm : 19 < m) (hn : k-l=(19:ℤ)*28) : False := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  have row := endpoint_case (s:=28) hf hg hn (by decide) hm grid_19_28
  simp only [keep_19_28,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=784 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1121_784_252 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=841 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1121_841_309 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=819 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1539_819_287 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1028 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1539_1028_496 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=584 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1767_584_52 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=964 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1767_964_432 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=983 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1767_983_451 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1743 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1767_1743_1211 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=709 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1957_709_177 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1488 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1957_1488_956 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=616 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3363_616_84 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=635 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3363_635_103 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2820 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3363_2820_2288 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2915 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3363_2915_2383 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=591 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5871_591_59 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5284 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5871_5284_4752 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=548 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7277_548_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7141 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7277_7141_6609 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=560 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10089_560_28 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=9585 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10089_9585_9053 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=541 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11533_541_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=11428 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11533_11428_10896 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=535 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20159_535_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=533 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28709_533_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=535 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_34599_535_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=34488 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_34599_34488_33956 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=533 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_60477_533_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=533 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_103797_533_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=103684 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_103797_103684_103152 G hg ⟨f,hf⟩

end Signed39.Contraction
