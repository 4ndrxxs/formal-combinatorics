import Signed29Grid23Part0
import Signed29Grid23Part12
import Signed29Grid23Part24
import Signed29Grid23Part36
import Signed29Grid23Part48
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_23_29 : divisorGrid 23 29 274 qInputs_23_29 keep_23_29 := by
  intro d
  fin_cases d
  · exact grid23x29Case0
  · exact grid23x29Case1
  · exact grid23x29Case2
  · exact grid23x29Case3
  · exact grid23x29Case4
  · exact grid23x29Case5
  · exact grid23x29Case6
  · exact grid23x29Case7
  · exact grid23x29Case8
  · exact grid23x29Case9
  · exact grid23x29Case10
  · exact grid23x29Case11
  · exact grid23x29Case12
  · exact grid23x29Case13
  · exact grid23x29Case14
  · exact grid23x29Case15
  · exact grid23x29Case16
  · exact grid23x29Case17
  · exact grid23x29Case18
  · exact grid23x29Case19
  · exact grid23x29Case20
  · exact grid23x29Case21
  · exact grid23x29Case22
  · exact grid23x29Case23
  · exact grid23x29Case24
  · exact grid23x29Case25
  · exact grid23x29Case26
  · exact grid23x29Case27
  · exact grid23x29Case28
  · exact grid23x29Case29
  · exact grid23x29Case30
  · exact grid23x29Case31
  · exact grid23x29Case32
  · exact grid23x29Case33
  · exact grid23x29Case34
  · exact grid23x29Case35
  · exact grid23x29Case36
  · exact grid23x29Case37
  · exact grid23x29Case38
  · exact grid23x29Case39
  · exact grid23x29Case40
  · exact grid23x29Case41
  · exact grid23x29Case42
  · exact grid23x29Case43
  · exact grid23x29Case44
  · exact grid23x29Case45
  · exact grid23x29Case46
  · exact grid23x29Case47
  · exact grid23x29Case48
  · exact grid23x29Case49
  · exact grid23x29Case50
  · exact grid23x29Case51
  · exact grid23x29Case52
  · exact grid23x29Case53
  · exact grid23x29Case54
  · exact grid23x29Case55
  · exact grid23x29Case56
  · exact grid23x29Case57



private theorem frontier_mixed_667_666_neg1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=667) : ¬∃ f : G → ℤ, IsSDS 666 (-1) f :=
  abelian_short_linear G 23 29 25 1 1 0 666 (-1) 29 0 2 5
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1127_734_67 : List RowType := [((-13),41),((-12),48),((-11),25),((-7),47),((-5),39),((-4),36),((-2),32),((-1),31),(0,0),(0,46),(1,31),(2,32),(4,36),(5,39),(7,47),(11,25),(12,48),(13,41),(17,35)]
private def stage_0_frontier_mixed_1127_734_67 : Stage := [
  (((-12),48),⟨⟨0,0,16513,(-8387)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],192⟩),
  (((-11),25),⟨⟨0,(-28497),0,(-6003)⟩,[0,0,0,0,0,0,0,0,0,0,0,626934,0,0,0,0,0,0,0,0,0,0,0],374⟩),
  (((-7),47),⟨⟨0,0,12005,(-11515)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],258⟩),
  (((-5),39),⟨⟨0,(-1470),0,(-510)⟩,[0,0,0,0,0,0,0,0,0,0,0,32340,0,0,0,0,0,20580,0,0,0,0,0],11⟩),
  (((-2),32),⟨⟨0,(-199479),0,(-22563)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,5186454,0,0,0,0,0,0,0,0,0],1105⟩),
  (((-1),31),⟨⟨0,0,0,(-943)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,181447,0,0,0,0,0],18⟩),
  ((1,31),⟨⟨0,0,0,(-943)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,181447,0,0,0,0,0],18⟩),
  ((5,39),⟨⟨0,(-1470),0,(-510)⟩,[0,0,0,0,0,0,0,0,0,0,0,32340,0,0,0,0,0,20580,0,0,0,0,0],11⟩),
  ((7,47),⟨⟨0,0,12005,(-11515)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],258⟩),
  ((11,25),⟨⟨0,(-28497),0,(-6003)⟩,[0,0,0,0,0,0,0,0,0,0,0,626934,0,0,0,0,0,0,0,0,0,0,0],374⟩),
  ((12,48),⟨⟨0,0,16513,(-8387)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],192⟩),
  ((13,41),⟨⟨0,0,0,(-989)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],24⟩),
  ((17,35),⟨⟨0,0,0,(-1311715080)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],35217917⟩)]
private theorem frontier_mixed_1127_734_67 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1127) : ¬∃ f : G → ℤ, IsSDS 734 67 f :=
  abelian_short_mixed G 23 49 25 1 1 0 734 67 29 12 2 5 32 15
    types_frontier_mixed_1127_734_67 [stage_0_frontier_mixed_1127_734_67] ⟨⟨4,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1541_716_49 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1541) : ¬∃ f : G → ℤ, IsSDS 716 49 f :=
  abelian_short_linear G 23 67 25 1 1 0 716 49 29 12 2 5
    ⟨⟨0,(-3082),528,103⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1840,3519,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1909_729_62 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1909) : ¬∃ f : G → ℤ, IsSDS 729 62 f :=
  abelian_short_linear G 23 83 25 2 1 0 729 62 29 15 2 5
    ⟨⟨0,(-874),240,19⟩,[0,0,0,0,0,0,0,0,0,0,0,0,552,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_2369_1024_357 : List RowType := [(15,33),(15,79),(16,40),(16,86),(17,43),(17,89),(18,42),(18,88),(19,37),(19,83),(20,74),(21,61),(22,44),(22,90),(23,69),(24,44),(24,90),(25,61),(26,74),(27,37),(27,83),(28,42),(28,88),(29,43),(29,89),(30,40),(30,86),(31,79),(32,68),(33,53),(33,99),(34,34),(34,80),(35,57),(35,103),(36,76),(37,45),(37,91),(38,56),(38,102),(39,63),(40,66),(41,65),(42,60),(43,51),(43,97),(44,84),(45,67),(46,46),(46,92),(47,67),(48,84),(49,51),(49,97),(50,60),(51,65),(52,66),(53,63),(54,56),(54,102),(55,91),(56,76),(57,57),(59,99),(60,68),(61,79),(65,83)]
private def stage_0_frontier_mixed_2369_1024_357 : Stage := [
  ((17,43),⟨⟨0,0,0,(-774)⟩,[0,0,0,0,0,0,0,0,0,0,392224,0,720588,0,176130,0,0,0,0,0,0,0,0],97⟩),
  ((21,61),⟨⟨(-307970),0,0,(-46)⟩,[0,52118,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108974,0,0,0,0],31⟩),
  ((23,69),⟨⟨(-30360),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((25,61),⟨⟨(-710700),0,15141,(-147)⟩,[0,0,0,0,108974,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],32⟩),
  ((28,88),⟨⟨(-3326076),0,75396,(-801)⟩,[0,0,0,248745,504597,0,239269,0,284280,0,0,0,0,0,0,0,0,0,0,135033,0,0,0],46⟩),
  ((34,34),⟨⟨296125,0,0,(-621)⟩,[0,0,0,0,0,0,0,0,0,0,0,187151,0,0,0,0,0,0,0,0,0,0,0],100⟩),
  ((37,45),⟨⟨(-31446106),0,0,4462⟩,[0,0,0,0,0,0,0,19662700,0,0,0,0,0,0,0,0,0,0,0,0,7812962,0,0],3311⟩),
  ((38,102),⟨⟨(-2158159),0,34402,(-81)⟩,[0,0,0,0,78177,452479,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,153985],47⟩),
  ((45,67),⟨⟨(-1032884),0,23793,(-415)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,99498,0,0,0,0,0,0,0],52⟩),
  ((46,46),⟨⟨(-2104702),0,0,748⟩,[0,0,0,0,0,77044,0,0,0,0,0,0,0,0,0,173452,84254,0,0,0,0,0,0],35⟩),
  ((47,67),⟨⟨(-2601162),0,80031,(-1191)⟩,[0,0,0,0,0,0,0,0,0,0,0,469062,0,0,0,0,0,0,0,0,0,0,0],74⟩),
  ((49,97),⟨⟨(-331660),0,4944,(-2)⟩,[52118,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,47380,0,0,0,0],5⟩),
  ((50,60),⟨⟨(-236900),0,0,(-25)⟩,[0,0,0,0,0,0,0,0,0,0,0,28325,0,0,0,77868,0,0,0,147393,0,0,0],42⟩),
  ((53,63),⟨⟨(-236900),0,0,(-25)⟩,[0,0,0,0,0,0,0,0,0,0,0,28325,0,0,0,77868,0,0,0,147393,0,0,0],42⟩),
  ((54,102),⟨⟨(-331660),0,4944,(-2)⟩,[52118,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,47380,0,0,0,0],5⟩),
  ((56,76),⟨⟨(-535394),0,13390,(-176)⟩,[0,0,0,0,0,75808,0,0,0,0,0,52118,0,0,4738,0,0,0,0,0,0,0,0],15⟩),
  ((59,99),⟨⟨(-682272),0,10197,(-53)⟩,[52118,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,222686,0,0,85284],9⟩)]
private theorem frontier_mixed_2369_1024_357 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2369) : ¬∃ f : G → ℤ, IsSDS 1024 357 f :=
  abelian_short_mixed G 23 103 25 1 1 0 1024 357 29 40 2 5 9 2
    types_frontier_mixed_2369_1024_357 [stage_0_frontier_mixed_2369_1024_357] ⟨⟨13478,(-989),121,12⟩,[0,0,0,0,0,0,0,552,0,0,0,0,0,0,0,0,0,0,0,0,690,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_2369_1553_886 : List RowType := [(38,56),(38,102),(39,63),(40,66),(41,65),(42,60),(43,51),(43,97),(44,84),(45,67),(46,46),(46,92),(47,67),(48,84),(49,51),(49,97),(50,60),(51,65),(52,66),(53,63),(54,56),(54,102),(55,91),(56,76),(57,57),(59,99),(60,68),(61,79),(65,83),(68,90),(69,69),(70,90)]
private def stage_0_frontier_mixed_2369_1553_886 : Stage := [
  ((42,60),⟨⟨0,0,0,(-30068768)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],6329995⟩),
  ((43,51),⟨⟨0,0,0,(-5819)⟩,[0,26802866,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1565909,0,0,0,0],729⟩),
  ((45,67),⟨⟨2383214,0,0,(-1334)⟩,[0,341136,0,0,0,0,0,0,0,0,0,0,0,2061030,933386,0,0,0,0,0,0,0,0],85⟩),
  ((51,65),⟨⟨175306,0,0,(-115)⟩,[0,0,0,0,0,0,0,0,0,0,0,130295,0,0,0,0,0,0,0,0,0,0,156354],29⟩),
  ((52,66),⟨⟨175306,0,0,(-115)⟩,[0,0,0,0,0,0,0,0,0,0,0,130295,0,0,0,0,0,0,0,0,0,0,156354],29⟩),
  ((61,79),⟨⟨0,(-2024),0,0⟩,[12696,71852,1104,0,0,2346,4370,0,3726,15272,0,5244,0,0,6900,37490,0,0,0,0,0,0,0],3⟩),
  ((68,90),⟨⟨(-8860060),0,267800,(-3635)⟩,[7005133,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,227424],147⟩),
  ((69,69),⟨⟨(-917332),0,9315,0⟩,[234715,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],17⟩),
  ((70,90),⟨⟨405099,0,0,(-483)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,845733,0,0,0,0,0,0,0,0],208⟩)]
private theorem frontier_mixed_2369_1553_886 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2369) : ¬∃ f : G → ℤ, IsSDS 1553 886 f :=
  abelian_short_mixed G 23 103 25 1 1 0 1553 886 29 63 2 5 9 2
    types_frontier_mixed_2369_1553_886 [stage_0_frontier_mixed_2369_1553_886] ⟨⟨0,0,4225,(-83)⟩,[0,0,0,0,0,0,0,0,5428,0,0,28842,0,0,11500,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2461_961_294 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2461) : ¬∃ f : G → ℤ, IsSDS 961 294 f :=
  abelian_short_linear G 23 107 25 2 1 0 961 294 29 37 2 5
    ⟨⟨(-34868),0,896,(-3)⟩,[0,0,0,0,0,1380,0,0,0,0,0,0,0,0,0,0,0,0,0,736,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2461_1720_1053 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2461) : ¬∃ f : G → ℤ, IsSDS 1720 1053 f :=
  abelian_short_linear G 23 107 25 1 1 0 1720 1053 29 70 2 5
    ⟨⟨(-8004),0,496,(-7)⟩,[0,0,0,644,0,0,0,0,0,0,0,0,0,0,0,3795,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4531_709_42 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4531) : ¬∃ f : G → ℤ, IsSDS 709 42 f :=
  abelian_short_linear G 23 197 25 4 1 0 709 42 29 19 2 5
    ⟨⟨0,(-8027),1800,203⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,21114,0,0,5244,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4531_4366_3699 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4531) : ¬∃ f : G → ℤ, IsSDS 4366 3699 f :=
  abelian_short_linear G 23 197 25 0 1 0 4366 3699 29 178 2 5
    ⟨⟨4775674,(-58581),3213,158⟩,[0,0,0,0,0,0,6486,8924,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5221_784_117 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5221) : ¬∃ f : G → ℤ, IsSDS 784 117 f :=
  abelian_short_linear G 23 227 25 0 1 0 784 117 29 34 2 5
    ⟨⟨(-46),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5221_4441_3774 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5221) : ¬∃ f : G → ℤ, IsSDS 4441 3774 f :=
  abelian_short_linear G 23 227 25 0 1 0 4441 3774 29 193 2 5
    ⟨⟨181,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6509_745_78 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6509) : ¬∃ f : G → ℤ, IsSDS 745 78 f :=
  abelian_short_linear G 23 283 25 0 1 0 745 78 29 31 2 5
    ⟨⟨0,(-798195),255580,11796⟩,[0,0,0,1533480,1450908,0,0,0,0,0,0,0,0,0,0,2563664,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6509_5828_5161 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6509) : ¬∃ f : G → ℤ, IsSDS 5828 5161 f :=
  abelian_short_linear G 23 283 25 0 1 0 5828 5161 29 252 2 5
    ⟨⟨237,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10787_674_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10787) : ¬∃ f : G → ℤ, IsSDS 674 7 f :=
  abelian_short_linear G 23 469 25 8 1 0 674 7 29 12 2 5
    ⟨⟨0,(-2599),231,74⟩,[0,0,0,0,0,0,1380,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13133_680_13 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13133) : ¬∃ f : G → ℤ, IsSDS 680 13 f :=
  abelian_short_linear G 23 571 25 5 1 0 680 13 29 18 2 5
    ⟨⟨(-162),(-28),3,1⟩,[162,0,10,54,0,0,0,18,0,0,0,0,0,18,22,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13133_12985_12318 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13133) : ¬∃ f : G → ℤ, IsSDS 12985 12318 f :=
  abelian_short_linear G 23 571 25 0 1 0 12985 12318 29 553 2 5
    ⟨⟨(-571),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14789_673_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14789) : ¬∃ f : G → ℤ, IsSDS 673 6 f :=
  abelian_short_linear G 23 643 25 8 1 0 673 6 29 13 2 5
    ⟨⟨0,(-1199),108,25⟩,[0,0,0,0,0,0,246,0,0,0,418,0,0,0,0,0,688,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23437_676_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23437) : ¬∃ f : G → ℤ, IsSDS 676 9 f :=
  abelian_short_linear G 23 1019 25 4 1 0 676 9 29 20 2 5
    ⟨⟨(-2298),(-1864),125,37⟩,[2298,0,878,0,662,0,1650,1158,0,0,0,0,338,0,392,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23437_23193_22526 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23437) : ¬∃ f : G → ℤ, IsSDS 23193 22526 f :=
  abelian_short_linear G 23 1019 25 0 1 0 23193 22526 29 999 2 5
    ⟨⟨(-1019),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_25369_673_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=25369) : ¬∃ f : G → ℤ, IsSDS 673 6 f :=
  abelian_short_linear G 23 1103 25 6 1 0 673 6 29 17 2 5
    ⟨⟨0,(-3887),209,94⟩,[0,0,0,0,0,3082,0,4002,0,0,2300,0,5520,2668,46,0,0,3174,1472,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_25369_25260_24593 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=25369) : ¬∃ f : G → ℤ, IsSDS 25260 24593 f :=
  abelian_short_linear G 23 1103 25 0 1 0 25260 24593 29 1086 2 5
    ⟨⟨(-1103),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_31717_673_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=31717) : ¬∃ f : G → ℤ, IsSDS 673 6 f :=
  abelian_short_linear G 23 1379 25 5 1 0 673 6 29 19 2 5
    ⟨⟨0,(-2668),175,37⟩,[0,0,0,0,0,0,230,0,0,0,230,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_31717_31516_30849 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=31717) : ¬∃ f : G → ℤ, IsSDS 31516 30849 f :=
  abelian_short_linear G 23 1379 25 0 1 0 31516 30849 29 1360 2 5
    ⟨⟨(-1379),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_75509_668_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=75509) : ¬∃ f : G → ℤ, IsSDS 668 1 f :=
  abelian_short_linear G 23 3283 25 8 1 0 668 1 29 12 2 5
    ⟨⟨(-190302),(-20631),3952,(-223)⟩,[190302,0,113896,123786,0,57960,0,0,0,0,0,0,19458,0,0,16422,0,0,0,0,0,31372,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_304037_668_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=304037) : ¬∃ f : G → ℤ, IsSDS 668 1 f :=
  abelian_short_linear G 23 13219 25 2 1 0 668 1 29 24 2 5
    ⟨⟨0,0,1,(-65)⟩,[0,0,184,506,920,1518,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_304037_303601_302934 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=304037) : ¬∃ f : G → ℤ, IsSDS 303601 302934 f :=
  abelian_short_linear G 23 13219 25 1 1 0 303601 302934 29 13195 2 5
    ⟨⟨(-13219),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_23_29_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=23*m)
    (hm : 23 < m) (hn : k-l=(23:ℤ)*29) : False := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have row := endpoint_case (s:=29) hf hg hn (by decide) hm grid_23_29
  simp only [keep_23_29,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=666 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_667_666_neg1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=734 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1127_734_67 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=716 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1541_716_49 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=729 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1909_729_62 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1024 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2369_1024_357 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1553 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2369_1553_886 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=961 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2461_961_294 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1720 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2461_1720_1053 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=709 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4531_709_42 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4366 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4531_4366_3699 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=784 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5221_784_117 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5221_4441_3774 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=745 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6509_745_78 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5828 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6509_5828_5161 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=674 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10787_674_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=680 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13133_680_13 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=12985 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13133_12985_12318 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=673 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14789_673_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=676 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23437_676_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=23193 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23437_23193_22526 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=673 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_25369_673_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=25260 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_25369_25260_24593 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=673 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_31717_673_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=31516 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_31717_31516_30849 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=668 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_75509_668_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=668 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_304037_668_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=303601 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_304037_303601_302934 G hg ⟨f,hf⟩

end Signed39.Contraction
