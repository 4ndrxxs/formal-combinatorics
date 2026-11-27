import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_11_16 : ℕ → Option QuotientInput
  | 37 => some ⟨37,11,3,0,16⟩
  | 53 => some ⟨53,11,13,0,16⟩
  | 97 => some ⟨97,11,24,0,16⟩
  | 113 => some ⟨113,11,28,0,16⟩
  | 259 => some ⟨37,11,3,0,16⟩
  | 1843 => some ⟨97,11,24,0,16⟩
  | _ => none

private def keep_11_16 : List (ℕ × ℤ) := [(19,20),(25,35),(35,25),(35,80),(35,113),(43,16),(49,32),(49,307),(83,1),(95,4),(107,20),(107,889),(125,7),(125,1184),(175,5),(175,16),(175,1589),(175,1732),(263,5),(263,2656),(271,4),(271,2765),(523,1),(535,4),(535,5581),(875,1),(875,9428),(1315,1),(1315,14224),(2459,1),(2459,26720)]

private theorem grid_11_16 : divisorGrid 11 16 103 qInputs_11_16 keep_11_16 := by decide +kernel

private theorem frontier_mixed_209_196_20 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=209) : ¬∃ f : G → ℤ, IsSDS 196 20 f :=
  abelian_short_linear G 11 19 12 1 2 5 196 20 16 6 10 29
    ⟨⟨(-12),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_275_211_35 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=275) : ¬∃ f : G → ℤ, IsSDS 211 35 f :=
  abelian_short_linear G 11 25 12 1 2 5 211 35 16 9 10 29
    ⟨⟨5,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_385_201_25 : List RowType := [((-3),21),((-1),17),(1,17),(3,21),(5,29),(7,19),(9,13),(11,33),(15,19),(17,29),(19,21)]
private def stage_0_frontier_mixed_385_201_25 : Stage := [
  (((-3),21),⟨⟨0,(-108108),4935,5073⟩,[239316,0,0,0,0,0,0,0,0,0,0],164⟩),
  (((-1),17),⟨⟨(-35475),0,900,23⟩,[0,0,0,0,0,0,0,0,0,11000,0],8⟩),
  ((1,17),⟨⟨(-35475),0,900,23⟩,[0,0,0,0,0,0,0,0,0,11000,0],8⟩),
  ((3,21),⟨⟨0,(-108108),4935,5073⟩,[239316,0,0,0,0,0,0,0,0,0,0],164⟩),
  ((5,29),⟨⟨(-15015),0,560,(-5)⟩,[0,0,0,0,0,0,0,4620,0,1540,0],2⟩),
  ((7,19),⟨⟨(-41303955),0,1365420,68271⟩,[0,0,0,0,0,0,0,0,0,0,0],8360⟩),
  ((9,13),⟨⟨0,(-19943),(-4851),1474⟩,[10626,0,0,0,0,0,0,0,0,95480,0],74⟩),
  ((11,33),⟨⟨0,(-35000),0,1000⟩,[0,0,0,0,0,0,0,0,0,0,0],91⟩),
  ((15,19),⟨⟨0,(-21560),(-1050),1240⟩,[0,0,0,0,0,0,0,110110,0,0,0],39⟩),
  ((17,29),⟨⟨(-52129),(-3696),1596,181⟩,[0,0,0,0,0,0,0,0,0,41272,0],12⟩),
  ((19,21),⟨⟨27720,(-30800),(-10605),2041⟩,[26180,0,0,184800,0,0,0,39270,0,0,0],116⟩)]
private theorem frontier_mixed_385_201_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=385) : ¬∃ f : G → ℤ, IsSDS 201 25 f :=
  abelian_short_mixed G 11 35 12 1 2 5 201 25 16 9 10 29 16 5
    types_frontier_mixed_385_201_25 [stage_0_frontier_mixed_385_201_25] ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_385_256_80 : List RowType := [(4,30),(6,18),(8,32),(10,28),(12,28),(14,32),(16,18),(18,30),(26,30)]
private def stage_0_frontier_mixed_385_256_80 : Stage := [
  ((4,30),⟨⟨0,(-216370),64260,2047⟩,[0,0,0,0,0,0,0,572880,0,0,0],692⟩),
  ((6,18),⟨⟨0,(-4466),0,(-275)⟩,[0,0,0,0,0,0,0,0,0,0,0],104⟩),
  ((8,32),⟨⟨103488,(-48510),4900,1389⟩,[0,48664,0,0,0,0,0,42504,0,0,0],68⟩),
  ((10,28),⟨⟨0,(-204050),58800,4975⟩,[0,0,0,0,0,754600,0,0,0,0,0],108⟩),
  ((12,28),⟨⟨(-3388),0,0,(-11)⟩,[0,0,0,0,1386,0,616,0,0,0,0],3⟩),
  ((14,32),⟨⟨(-323400),0,7840,(-147)⟩,[0,0,0,0,0,32340,0,10780,0,0,118580],58⟩),
  ((16,18),⟨⟨338778,0,(-87261),880⟩,[0,0,0,0,0,677556,0,0,0,0,564630],880⟩),
  ((18,30),⟨⟨0,(-47355),1890,1629⟩,[0,20790,0,65450,0,0,0,130130,20790,0,0],101⟩),
  ((26,30),⟨⟨(-147840),0,3610,43⟩,[0,0,0,0,0,18260,0,5280,0,0,0],28⟩)]
private theorem frontier_mixed_385_256_80 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=385) : ¬∃ f : G → ℤ, IsSDS 256 80 f :=
  abelian_short_mixed G 11 35 12 1 2 5 256 80 16 16 10 29 16 5
    types_frontier_mixed_385_256_80 [stage_0_frontier_mixed_385_256_80] ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_385_289_113 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=385) : ¬∃ f : G → ℤ, IsSDS 289 113 f :=
  abelian_short_linear G 11 35 12 1 2 5 289 113 16 19 10 29
    ⟨⟨0,15,0,(-1)⟩,[0,0,0,0,0,0,34,0,76,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_473_192_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=473) : ¬∃ f : G → ℤ, IsSDS 192 16 f :=
  abelian_short_linear G 11 43 12 2 2 5 192 16 16 8 10 29
    ⟨⟨0,(-195833),26236,10780⟩,[0,0,0,0,0,0,0,0,247368,0,41228],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_539_208_32 : List RowType := [(0,0),(0,22),(0,44),(2,14),(2,36),(4,34),(6,16),(6,38),(8,26),(8,48),(10,20),(10,42),(12,20),(12,42),(14,26),(14,48),(16,16),(16,38),(18,34),(20,36),(22,22),(22,44),(24,36)]
private def stage_0_frontier_mixed_539_208_32 : Stage := [
  ((0,0),⟨⟨127440,(-23895),864,944⟩,[0,6372,0,0,0,0,0,0,0,0,0],0⟩),
  ((0,22),⟨⟨191760,(-35955),1316,1428⟩,[0,9588,0,0,0,0,0,0,0,0,0],0⟩),
  ((0,44),⟨⟨0,(-34),12,1⟩,[0,24,0,0,0,96,0,0,0,0,0],0⟩),
  ((2,14),⟨⟨(-11841885),0,0,(-38565)⟩,[11841885,0,0,0,0,0,0,0,0,0,0],9427⟩),
  ((2,36),⟨⟨0,(-578886),113484,20091⟩,[0,125048,0,375144,0,1565256,0,0,0,0,0],260⟩),
  ((4,34),⟨⟨0,(-18171000),0,570000⟩,[0,0,0,0,11441000,0,0,0,11441000,0,0],38361⟩),
  ((6,16),⟨⟨0,(-1573288750),55365000,69300000⟩,[0,0,0,0,0,0,0,0,0,0,6800667500],2557863⟩),
  ((6,38),⟨⟨0,(-36135000),6752500,1122000⟩,[0,0,0,0,0,0,0,0,0,0,98367500],31317⟩),
  ((8,26),⟨⟨0,(-3234),0,99⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((8,48),⟨⟨0,(-3234),0,99⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((10,20),⟨⟨0,(-451687500),134685000,8866000⟩,[0,987690000,0,0,0,0,0,0,0,0,0],672111⟩),
  ((10,42),⟨⟨0,(-80850),24108,1587⟩,[0,176792,0,0,0,0,0,0,0,0,0],80⟩),
  ((12,20),⟨⟨0,(-3157),0,143⟩,[0,0,0,6468,0,0,0,0,0,0,14168],3⟩),
  ((12,42),⟨⟨0,(-27489),5145,753⟩,[0,0,0,0,0,0,0,0,0,0,63602],32⟩),
  ((14,26),⟨⟨0,(-673750),122500,31875⟩,[0,385000,0,0,0,0,0,0,0,0,0],242⟩),
  ((14,48),⟨⟨0,(-52822),9604,2499⟩,[0,30184,0,0,0,0,0,0,0,0,0],16⟩),
  ((16,16),⟨⟨0,(-1617),0,99⟩,[0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((16,38),⟨⟨0,(-367500),0,22500⟩,[0,0,0,0,0,0,0,0,0,0,0],343⟩),
  ((18,34),⟨⟨0,(-104566),0,5401⟩,[0,0,0,0,0,0,0,0,0,0,323400],120⟩),
  ((20,36),⟨⟨0,(-180026),42336,4295⟩,[0,219912,0,0,0,0,0,0,0,0,0],240⟩),
  ((22,22),⟨⟨0,(-1078),0,44⟩,[0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((22,44),⟨⟨0,(-1078),0,44⟩,[0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((24,36),⟨⟨0,(-8552565),0,379400⟩,[0,27248172,0,0,0,0,0,0,0,0,30609180],8574⟩)]
private theorem frontier_mixed_539_208_32 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=539) : ¬∃ f : G → ℤ, IsSDS 208 32 f :=
  abelian_short_mixed G 11 49 12 2 2 5 208 32 16 12 10 29 9 2
    types_frontier_mixed_539_208_32 [stage_0_frontier_mixed_539_208_32] ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_539_483_307 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=539) : ¬∃ f : G → ℤ, IsSDS 483 307 f :=
  abelian_short_linear G 11 49 12 1 2 5 483 307 16 37 10 29
    ⟨⟨1617,(-82),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_913_177_1 : List RowType := [((-9),19),((-9),41),((-9),63),((-7),21),((-7),43),((-7),65),((-5),17),((-5),39),((-5),61),((-5),83),((-3),29),((-3),51),((-3),73),((-1),13),((-1),35),((-1),57),((-1),79),(1,13),(1,35),(1,57),(1,79),(3,29),(3,51),(3,73),(5,17),(5,39),(5,61),(5,83),(7,21),(7,43),(7,65),(9,19),(9,41),(9,63),(11,33),(11,55),(11,77),(13,19),(13,41),(13,63),(15,21),(15,43),(15,65)]
private def stage_0_frontier_mixed_913_177_1 : Stage := [
  (((-9),41),⟨⟨(-1551187),(-69388),26062,8145⟩,[0,138776,0,416328,0,693880,0,0,0,0,0],64⟩),
  (((-9),63),⟨⟨(-1444366),(-44737),39093,4820⟩,[0,89474,0,0,0,447370,0,0,0,0,0],50⟩),
  (((-7),21),⟨⟨(-362793),(-6640),0,1865⟩,[69720,13280,0,69720,0,0,0,92960,29880,0,0],24⟩),
  (((-7),43),⟨⟨(-362793),(-6640),0,1865⟩,[69720,13280,0,69720,0,0,0,92960,29880,0,0],24⟩),
  (((-7),65),⟨⟨(-1622401),(-18260),0,9845⟩,[0,36520,0,255640,0,0,0,255640,146080,0,0],108⟩),
  (((-5),17),⟨⟨(-26477),0,0,77⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  (((-5),39),⟨⟨(-26477),0,0,77⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  (((-5),61),⟨⟨(-49302),(-14608),0,1694⟩,[0,29216,0,0,0,0,0,0,0,0,0],5⟩),
  (((-5),83),⟨⟨(-825),(-44),60,1⟩,[0,88,88,0,0,0,0,0,0,0,0],0⟩),
  (((-3),29),⟨⟨(-75779),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  (((-3),51),⟨⟨(-75779),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  (((-3),73),⟨⟨(-75779),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  (((-1),13),⟨⟨(-881045),(-25564),0,9009⟩,[0,0,0,0,0,255640,0,0,0,0,0],80⟩),
  (((-1),35),⟨⟨(-1127555),(-38346),0,12089⟩,[0,76692,0,0,0,383460,0,0,0,0,0],96⟩),
  (((-1),57),⟨⟨(-1127555),(-38346),0,12089⟩,[0,76692,0,0,0,383460,0,0,0,0,0],96⟩),
  (((-1),79),⟨⟨(-742269),(-12782),28552,(-729)⟩,[0,25564,0,0,0,127820,0,0,0,0,0],32⟩),
  ((1,13),⟨⟨(-881045),(-25564),0,9009⟩,[0,0,0,0,0,255640,0,0,0,0,0],80⟩),
  ((1,35),⟨⟨(-1127555),(-38346),0,12089⟩,[0,76692,0,0,0,383460,0,0,0,0,0],96⟩),
  ((1,57),⟨⟨(-1127555),(-38346),0,12089⟩,[0,76692,0,0,0,383460,0,0,0,0,0],96⟩),
  ((1,79),⟨⟨(-825),(-44),60,1⟩,[0,88,88,0,0,0,0,0,0,0,0],0⟩),
  ((3,29),⟨⟨(-75779),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((3,51),⟨⟨(-75779),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((3,73),⟨⟨(-75779),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((5,17),⟨⟨(-26477),0,0,77⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((5,39),⟨⟨(-26477),0,0,77⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((5,61),⟨⟨(-110473),0,4482,(-593)⟩,[0,0,10956,0,0,0,0,0,0,3652,0],8⟩),
  ((5,83),⟨⟨(-825),(-44),60,1⟩,[0,88,88,0,0,0,0,0,0,0,0],0⟩),
  ((7,21),⟨⟨(-362793),(-6640),0,1865⟩,[69720,13280,0,69720,0,0,0,92960,29880,0,0],24⟩),
  ((7,43),⟨⟨(-362793),(-6640),0,1865⟩,[69720,13280,0,69720,0,0,0,92960,29880,0,0],24⟩),
  ((7,65),⟨⟨(-1622401),(-18260),0,9845⟩,[0,36520,0,255640,0,0,0,255640,146080,0,0],108⟩),
  ((9,41),⟨⟨(-1527449),0,35524,1717⟩,[0,0,0,0,0,357896,357896,0,0,0,0],60⟩),
  ((9,63),⟨⟨(-1444366),(-44737),39093,4820⟩,[0,89474,0,0,0,447370,0,0,0,0,0],50⟩),
  ((11,55),⟨⟨(-2321),(-132),168,5⟩,[0,264,0,0,0,0,0,0,0,0,0],0⟩),
  ((11,77),⟨⟨(-825),(-44),60,1⟩,[0,88,88,0,0,0,0,0,0,0,0],0⟩),
  ((13,19),⟨⟨(-789745),0,23572,981⟩,[0,0,0,0,0,0,0,0,0,0,0],28⟩),
  ((13,41),⟨⟨(-789745),0,23572,981⟩,[0,0,0,0,0,0,0,0,0,0,0],28⟩),
  ((13,63),⟨⟨(-789745),0,23572,981⟩,[0,0,0,0,0,0,0,0,0,0,0],28⟩),
  ((15,21),⟨⟨(-30129),(-1826),0,803⟩,[0,0,0,10956,0,0,0,0,0,0,0],2⟩),
  ((15,43),⟨⟨(-126907),0,0,2299⟩,[0,0,0,36520,0,0,0,0,36520,0,0],8⟩),
  ((15,65),⟨⟨(-126907),0,0,2299⟩,[0,0,0,36520,0,0,0,0,36520,0,0],8⟩)]
private theorem frontier_mixed_913_177_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=913) : ¬∃ f : G → ℤ, IsSDS 177 1 f :=
  abelian_short_mixed G 11 83 12 4 2 5 177 1 16 3 10 29 68 9
    types_frontier_mixed_913_177_1 [stage_0_frontier_mixed_913_177_1] ⟨⟨(-19),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1045_180_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1045) : ¬∃ f : G → ℤ, IsSDS 180 4 f :=
  abelian_short_linear G 11 95 12 4 2 5 180 4 16 6 10 29
    ⟨⟨0,(-22),4,1⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1177_196_20 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1177) : ¬∃ f : G → ℤ, IsSDS 196 20 f :=
  abelian_short_linear G 11 107 12 1 2 5 196 20 16 14 10 29
    ⟨⟨(-2173732),(-64185),81690,3696⟩,[0,0,0,0,410784,0,0,171160,0,0,975612],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1177_1065_889 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1177) : ¬∃ f : G → ℤ, IsSDS 1065 889 f :=
  abelian_short_linear G 11 107 12 1 2 5 1065 889 16 93 10 29
    ⟨⟨89,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1375_183_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1375) : ¬∃ f : G → ℤ, IsSDS 183 7 f :=
  abelian_short_linear G 11 125 12 3 2 5 183 7 16 9 10 29
    ⟨⟨(-4560114780),(-415341558),198251586,19670092⟩,[207670779,0,2076707790,276894372,0,0,0,0,0,2145931383,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1375_1360_1184 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1375) : ¬∃ f : G → ℤ, IsSDS 1360 1184 f :=
  abelian_short_linear G 11 125 12 0 2 5 1360 1184 16 116 10 29
    ⟨⟨112,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1925_181_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1925) : ¬∃ f : G → ℤ, IsSDS 181 5 f :=
  abelian_short_linear G 11 175 12 3 2 5 181 5 16 9 10 29
    ⟨⟨(-5431500),(-1011750),305000,38979⟩,[1810500,0,3195000,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1925_192_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1925) : ¬∃ f : G → ℤ, IsSDS 192 16 f :=
  abelian_short_linear G 11 175 12 0 2 5 192 16 16 16 10 29
    ⟨⟨(-22),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1925_1765_1589 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1925) : ¬∃ f : G → ℤ, IsSDS 1765 1589 f :=
  abelian_short_linear G 11 175 12 0 2 5 1765 1589 16 159 10 29
    ⟨⟨153,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1925_1908_1732 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1925) : ¬∃ f : G → ℤ, IsSDS 1908 1732 f :=
  abelian_short_linear G 11 175 12 0 2 5 1908 1732 16 166 10 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2893_181_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2893) : ¬∃ f : G → ℤ, IsSDS 181 5 f :=
  abelian_short_linear G 11 263 12 2 2 5 181 5 16 11 10 29
    ⟨⟨(-5247),(-2420),360,107⟩,[0,0,264,0,0,0,704,2904,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2893_2832_2656 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2893) : ¬∃ f : G → ℤ, IsSDS 2832 2656 f :=
  abelian_short_linear G 11 263 12 1 2 5 2832 2656 16 252 10 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2981_180_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2981) : ¬∃ f : G → ℤ, IsSDS 180 4 f :=
  abelian_short_linear G 11 271 12 3 2 5 180 4 16 10 10 29
    ⟨⟨(-1040),0,33,0⟩,[1040,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2981_2941_2765 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2981) : ¬∃ f : G → ℤ, IsSDS 2941 2765 f :=
  abelian_short_linear G 11 271 12 1 2 5 2941 2765 16 261 10 29
    ⟨⟨(-271),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5753_177_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5753) : ¬∃ f : G → ℤ, IsSDS 177 1 f :=
  abelian_short_linear G 11 523 12 4 2 5 177 1 16 7 10 29
    ⟨⟨(-268125),(-71500),15000,2574⟩,[33000,143000,0,33000,0,0,0,44000,0,165000,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5885_180_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5885) : ¬∃ f : G → ℤ, IsSDS 180 4 f :=
  abelian_short_linear G 11 535 12 1 2 5 180 4 16 14 10 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5885_5757_5581 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5885) : ¬∃ f : G → ℤ, IsSDS 5757 5581 f :=
  abelian_short_linear G 11 535 12 1 2 5 5757 5581 16 521 10 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9625_177_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9625) : ¬∃ f : G → ℤ, IsSDS 177 1 f :=
  abelian_short_linear G 11 875 12 3 2 5 177 1 16 9 10 29
    ⟨⟨0,(-44),5,1⟩,[0,0,0,0,0,0,0,44,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9625_9604_9428 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9625) : ¬∃ f : G → ℤ, IsSDS 9604 9428 f :=
  abelian_short_linear G 11 875 12 0 2 5 9604 9428 16 866 10 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14465_177_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14465) : ¬∃ f : G → ℤ, IsSDS 177 1 f :=
  abelian_short_linear G 11 1315 12 2 2 5 177 1 16 11 10 29
    ⟨⟨1,0,0,(-1)⟩,[0,0,0,8,0,24,0,0,0,80,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14465_14400_14224 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14465) : ¬∃ f : G → ℤ, IsSDS 14400 14224 f :=
  abelian_short_linear G 11 1315 12 1 2 5 14400 14224 16 1304 10 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_27049_177_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=27049) : ¬∃ f : G → ℤ, IsSDS 177 1 f :=
  abelian_short_linear G 11 2459 12 0 2 5 177 1 16 15 10 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_27049_26896_26720 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=27049) : ¬∃ f : G → ℤ, IsSDS 26896 26720 f :=
  abelian_short_linear G 11 2459 12 0 2 5 26896 26720 16 2444 10 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_11_16_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=11*m)
    (hm : 11 < m) (hn : k-l=(11:ℤ)*16) : False := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have row := endpoint_case (s:=16) hf hg hn (by decide) hm grid_11_16
  simp only [keep_11_16,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=196 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_209_196_20 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=211 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_275_211_35 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=201 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_385_201_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=256 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_385_256_80 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=289 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_385_289_113 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=192 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_473_192_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=208 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_539_208_32 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=483 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_539_483_307 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_913_177_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=180 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1045_180_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=196 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1177_196_20 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1065 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1177_1065_889 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=183 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1375_183_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1360 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1375_1360_1184 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=181 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1925_181_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=192 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1925_192_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1765 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1925_1765_1589 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1908 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1925_1908_1732 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=181 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2893_181_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2832 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2893_2832_2656 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=180 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2981_180_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2941 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2981_2941_2765 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5753_177_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=180 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5885_180_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5757 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5885_5757_5581 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9625_177_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=9604 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9625_9604_9428 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14465_177_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=14400 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14465_14400_14224 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_27049_177_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=26896 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_27049_26896_26720 G hg ⟨f,hf⟩

end Signed39.Contraction
