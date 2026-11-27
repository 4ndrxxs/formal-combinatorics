import Signed25Grid7Part0
import Signed25Grid7Part12
import Signed25Grid7Part24
import Signed25Grid7Part36
import Signed25Grid7Part48
import SignedAlmostBinary
import SignedLong413
import SignedShortFibres
import SignedLong413
import Signed25Case987W178
import Signed25Case1589W176
import Signed25Case1897W177
import Signed25Case2961W176
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_7_25 : divisorGrid 7 25 130 qInputs_7_25 keep_7_25 := by
  intro d
  fin_cases d
  · exact grid7x25Case0
  · exact grid7x25Case1
  · exact grid7x25Case2
  · exact grid7x25Case3
  · exact grid7x25Case4
  · exact grid7x25Case5
  · exact grid7x25Case6
  · exact grid7x25Case7
  · exact grid7x25Case8
  · exact grid7x25Case9
  · exact grid7x25Case10
  · exact grid7x25Case11
  · exact grid7x25Case12
  · exact grid7x25Case13
  · exact grid7x25Case14
  · exact grid7x25Case15
  · exact grid7x25Case16
  · exact grid7x25Case17
  · exact grid7x25Case18
  · exact grid7x25Case19
  · exact grid7x25Case20
  · exact grid7x25Case21
  · exact grid7x25Case22
  · exact grid7x25Case23
  · exact grid7x25Case24
  · exact grid7x25Case25
  · exact grid7x25Case26
  · exact grid7x25Case27
  · exact grid7x25Case28
  · exact grid7x25Case29
  · exact grid7x25Case30
  · exact grid7x25Case31
  · exact grid7x25Case32
  · exact grid7x25Case33
  · exact grid7x25Case34
  · exact grid7x25Case35
  · exact grid7x25Case36
  · exact grid7x25Case37
  · exact grid7x25Case38
  · exact grid7x25Case39
  · exact grid7x25Case40
  · exact grid7x25Case41
  · exact grid7x25Case42
  · exact grid7x25Case43
  · exact grid7x25Case44
  · exact grid7x25Case45
  · exact grid7x25Case46
  · exact grid7x25Case47
  · exact grid7x25Case48
  · exact grid7x25Case49



private theorem frontier_mixed_259_229_54 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=259) : ¬∃ f : G → ℤ, IsSDS 229 54 f :=
  abelian_short_linear G 7 37 12 2 5 3 229 54 25 17 1 7
    ⟨⟨1218,(-63),(-25),2⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_259_250_75 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=259) : ¬∃ f : G → ℤ, IsSDS 250 75 f :=
  abelian_short_linear G 7 37 12 2 5 3 250 75 25 20 1 7
    ⟨⟨200,(-2),(-5),0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_329_184_9 : List RowType := [((-2),12),((-2),26),((-2),40),(3,13),(3,27),(3,41),(8,24),(8,38),(13,17),(13,31),(13,45),(18,20),(18,34)]
private def stage_0_frontier_mixed_329_184_9 : Stage := [
  (((-2),12),⟨⟨(-90804),(-3619),0,679⟩,[0,16450,0,0,0,0,0],25⟩),
  (((-2),26),⟨⟨39,(-16),0,1⟩,[0,25,0,0,0,0,0],0⟩),
  (((-2),40),⟨⟨39,(-16),0,1⟩,[0,25,0,0,0,0,0],0⟩),
  ((3,13),⟨⟨33558,(-78302),0,4172⟩,[0,131600,0,0,0,0,0],75⟩),
  ((13,17),⟨⟨(-35532),(-9212),0,812⟩,[0,13160,0,0,0,0,0],15⟩),
  ((18,20),⟨⟨39,(-16),0,1⟩,[0,25,0,0,0,0,0],0⟩),
  ((18,34),⟨⟨39,(-16),0,1⟩,[0,25,0,0,0,0,0],0⟩)]
private theorem frontier_mixed_329_184_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=329) : ¬∃ f : G → ℤ, IsSDS 184 9 f :=
  abelian_short_mixed G 7 47 12 3 5 3 184 9 25 8 1 7 27 4
    types_frontier_mixed_329_184_9 [stage_0_frontier_mixed_329_184_9] ⟨⟨(-129),(-2),5,0⟩,[0,25,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_399_234_59 : List RowType := [(12,18),(12,32),(12,46),(17,23),(17,37),(17,51),(22,22),(22,36),(22,50),(27,29),(27,43),(27,57),(32,44)]
private def stage_0_frontier_mixed_399_234_59 : Stage := [
  ((12,18),⟨⟨452466,(-55461),0,1239⟩,[0,139650,0,0,0,0,0],25⟩),
  ((12,32),⟨⟨459,(-44),0,1⟩,[0,25,0,0,0,0,0],0⟩),
  ((12,46),⟨⟨459,(-44),0,1⟩,[0,25,0,0,0,0,0],0⟩),
  ((17,23),⟨⟨(-170400),0,0,0⟩,[0,0,0,0,16000,0,0],37⟩),
  ((22,22),⟨⟨513114,(-60914),0,1316⟩,[0,152950,0,0,0,0,39900],25⟩),
  ((27,29),⟨⟨(-954000),0,0,211⟩,[0,0,0,0,20000,0,0],211⟩),
  ((32,44),⟨⟨459,(-44),0,1⟩,[0,25,0,0,0,0,0],0⟩)]
private theorem frontier_mixed_399_234_59 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=399) : ¬∃ f : G → ℤ, IsSDS 234 59 f :=
  abelian_short_mixed G 7 57 12 3 5 3 234 59 25 22 1 7 49 6
    types_frontier_mixed_399_234_59 [stage_0_frontier_mixed_399_234_59] ⟨⟨(-36),0,1,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_399_325_150 : List RowType := [(25,37),(25,51),(30,32),(30,46),(35,35),(35,49),(40,46)]
private def stage_0_frontier_mixed_399_325_150 : Stage := [
  ((25,37),⟨⟨178,(-1),(-3),0⟩,[4,0,0,0,0,0,0],0⟩),
  ((25,51),⟨⟨1200,(-70),0,1⟩,[25,0,0,0,0,0,0],0⟩),
  ((30,32),⟨⟨(-4410),0,0,0⟩,[0,0,0,0,0,0,0],1⟩),
  ((35,35),⟨⟨1890,(-70),(-15),1⟩,[70,0,0,0,0,0,0],0⟩),
  ((40,46),⟨⟨(-740000),0,0,0⟩,[0,0,0,0,0,0,0],159⟩)]
private theorem frontier_mixed_399_325_150 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=399) : ¬∃ f : G → ℤ, IsSDS 325 150 f :=
  abelian_short_mixed G 7 57 12 2 5 3 325 150 25 35 1 7 49 6
    types_frontier_mixed_399_325_150 [stage_0_frontier_mixed_399_325_150] ⟨⟨(-140),(-3),5,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_399_381_206 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=399) : ¬∃ f : G → ℤ, IsSDS 381 206 f :=
  abelian_short_linear G 7 57 12 2 5 3 381 206 25 41 1 7
    ⟨⟨(-1271),72,0,(-1)⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_567_293_118 : List RowType := [(27,37),(27,51),(32,32),(32,46),(32,60),(37,43),(37,57),(37,71),(42,42),(42,56),(42,70),(47,57),(47,71)]
private def stage_0_frontier_mixed_567_293_118 : Stage := [
  ((27,37),⟨⟨1344,(-74),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((27,51),⟨⟨233856,(-13601),725,175⟩,[0,0,0,0,0,0,0],0⟩),
  ((32,32),⟨⟨(-10302957),0,0,3773⟩,[0,0,0,0,337365,0,0],740⟩),
  ((37,43),⟨⟨(-45927),0,0,7⟩,[0,0,0,0,9639,0,0],4⟩),
  ((42,42),⟨⟨5419386,(-324891),0,4599⟩,[0,0,85050,0,0,0,0],25⟩),
  ((47,57),⟨⟨1344,(-74),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((47,71),⟨⟨1344,(-74),0,1⟩,[0,0,25,0,0,0,0],0⟩)]
private theorem frontier_mixed_567_293_118 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=567) : ¬∃ f : G → ℤ, IsSDS 293 118 f :=
  abelian_short_mixed G 7 81 12 2 5 3 293 118 25 37 1 7 58 5
    types_frontier_mixed_567_293_118 [stage_0_frontier_mixed_567_293_118] ⟨⟨(-46),0,1,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_567_342_167 : List RowType := [(34,44),(34,58),(39,39),(39,53),(39,67),(44,50),(44,64),(44,78),(49,49),(49,63),(49,77),(54,64),(54,78)]
private def stage_0_frontier_mixed_567_342_167 : Stage := [
  ((34,44),⟨⟨1911,(-88),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((34,58),⟨⟨1911,(-88),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((39,39),⟨⟨9277254,(-420147),0,4599⟩,[0,0,85050,0,0,0,0],25⟩),
  ((44,50),⟨⟨(-1041012),0,0,(-259)⟩,[381591,0,0,0,0,0,0],176⟩),
  ((49,49),⟨⟨0,(-1178),0,0⟩,[0,0,872,0,0,0,21432],7⟩),
  ((54,64),⟨⟨1911,(-88),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((54,78),⟨⟨1911,(-88),0,1⟩,[0,0,25,0,0,0,0],0⟩)]
private theorem frontier_mixed_567_342_167 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=567) : ¬∃ f : G → ℤ, IsSDS 342 167 f :=
  abelian_short_mixed G 7 81 12 2 5 3 342 167 25 44 1 7 58 5
    types_frontier_mixed_567_342_167 [stage_0_frontier_mixed_567_342_167] ⟨⟨(-53),0,1,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_581_284_109 : List RowType := [(26,38),(26,52),(31,33),(31,47),(31,61),(36,48),(36,62),(41,41),(41,55),(41,69),(46,54),(46,68)]
private def stage_0_frontier_mixed_581_284_109 : Stage := [
  ((26,38),⟨⟨5964,(-343),25,4⟩,[0,0,0,0,0,0,350],0⟩),
  ((26,52),⟨⟨(-854),0,55,(-1)⟩,[0,0,0,0,0,0,280],0⟩),
  ((31,33),⟨⟨0,(-3486),0,63⟩,[0,0,0,36603,0,0,1743],4⟩),
  ((31,61),⟨⟨(-2744),0,90,(-1)⟩,[0,0,0,735,0,0,735],0⟩),
  ((36,48),⟨⟨(-28000),0,0,(-3)⟩,[0,0,0,0,0,0,0],3⟩),
  ((41,69),⟨⟨(-86),(-4),5,0⟩,[0,0,0,45,0,0,45],0⟩),
  ((46,54),⟨⟨3444,(-273),25,4⟩,[0,0,0,350,0,0,0],0⟩),
  ((46,68),⟨⟨(-164),(-1),5,0⟩,[0,0,0,30,0,0,0],0⟩)]
private theorem frontier_mixed_581_284_109 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=581) : ¬∃ f : G → ℤ, IsSDS 284 109 f :=
  abelian_short_mixed G 7 83 12 2 5 3 284 109 25 36 1 7 12 1
    types_frontier_mixed_581_284_109 [stage_0_frontier_mixed_581_284_109] ⟨⟨(-41),0,1,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_581_361_186 : List RowType := [(37,45),(37,59),(42,42),(42,56),(42,70),(47,59),(47,73),(52,54),(52,68),(52,82),(57,69)]
private def stage_0_frontier_mixed_581_361_186 : Stage := [
  ((37,45),⟨⟨10416,(-441),25,4⟩,[0,0,0,350,0,0,0],0⟩),
  ((37,59),⟨⟨(-546),0,55,(-1)⟩,[0,0,0,280,0,0,0],0⟩),
  ((42,70),⟨⟨(-6468),0,235,(-3)⟩,[1890,0,0,1890,0,0,0],0⟩),
  ((47,59),⟨⟨(-2964843),0,0,147⟩,[0,0,0,0,0,0,0],235⟩),
  ((52,54),⟨⟨144669,(-6972),0,63⟩,[1743,0,0,36603,0,0,0],4⟩),
  ((52,82),⟨⟨(-6468),0,235,(-3)⟩,[1890,0,0,1890,0,0,0],0⟩),
  ((57,69),⟨⟨7126,(-371),25,4⟩,[350,0,0,0,0,0,0],0⟩)]
private theorem frontier_mixed_581_361_186 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=581) : ¬∃ f : G → ℤ, IsSDS 361 186 f :=
  abelian_short_mixed G 7 83 12 2 5 3 361 186 25 47 1 7 12 1
    types_frontier_mixed_581_361_186 [stage_0_frontier_mixed_581_361_186] ⟨⟨12432,(-480),185,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_609_176_1 : List RowType := [((-6),12),((-6),26),((-6),40),((-6),54),((-6),68),((-6),82),((-1),19),((-1),33),((-1),47),((-1),61),((-1),75),(4,10),(4,24),(4,38),(4,52),(4,66),(4,80),(9,13),(9,27),(9,41),(9,55),(9,69),(9,83),(14,14),(14,28),(14,42),(14,56),(14,70),(14,84)]
private def stage_0_frontier_mixed_609_176_1 : Stage := [
  (((-6),12),⟨⟨(-295974),(-28623),0,2751⟩,[0,0,0,0,243600,0,0],25⟩),
  (((-6),26),⟨⟨(-89297640),(-8635780),0,830000⟩,[0,0,0,0,73496000,0,0],9187⟩),
  (((-6),40),⟨⟨(-9),(-8),0,1⟩,[0,0,0,0,25,0,0],0⟩),
  (((-6),54),⟨⟨(-9),(-8),0,1⟩,[0,0,0,0,25,0,0],0⟩),
  (((-6),68),⟨⟨(-9),(-8),0,1⟩,[0,0,0,0,25,0,0],0⟩),
  (((-6),82),⟨⟨(-9),(-8),0,1⟩,[0,0,0,0,25,0,0],0⟩),
  (((-1),19),⟨⟨(-4296190000),0,0,19526250⟩,[0,0,0,0,1329480000,0,0],469011⟩),
  ((4,10),⟨⟨(-69426),(-1827),0,259⟩,[0,0,0,0,0,0,0],10⟩),
  ((4,24),⟨⟨(-211932),(-40194),0,3388⟩,[0,0,0,0,0,0,0],25⟩),
  ((9,13),⟨⟨(-836766),0,0,1386⟩,[0,0,36540,0,36540,0,0],65⟩),
  ((9,27),⟨⟨(-317898),3654,0,252⟩,[0,0,0,0,0,0,0],25⟩),
  ((14,14),⟨⟨(-9184),(-3234),0,0⟩,[0,0,0,0,0,0,0],5⟩),
  ((14,28),⟨⟨(-9),(-8),0,1⟩,[0,0,0,0,25,0,0],0⟩),
  ((14,42),⟨⟨(-9),(-8),0,1⟩,[0,0,0,0,25,0,0],0⟩),
  ((14,56),⟨⟨(-9),(-8),0,1⟩,[0,0,0,0,25,0,0],0⟩),
  ((14,70),⟨⟨(-9),(-8),0,1⟩,[0,0,0,0,25,0,0],0⟩),
  ((14,84),⟨⟨(-9),(-8),0,1⟩,[0,0,0,0,25,0,0],0⟩)]
private theorem frontier_mixed_609_176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=609) : ¬∃ f : G → ℤ, IsSDS 176 1 f :=
  abelian_short_mixed G 7 87 12 6 5 3 176 1 25 4 1 7 25 2
    types_frontier_mixed_609_176_1 [stage_0_frontier_mixed_609_176_1] ⟨⟨(-33),0,1,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_609_225_50 : List RowType := [(15,19),(15,33),(15,47),(15,61),(20,26),(20,40),(20,54),(20,68),(25,31),(25,45),(25,59),(25,73),(30,34),(30,48),(30,62),(30,76),(35,35),(35,49),(35,63),(35,77)]
private def stage_0_frontier_mixed_609_225_50 : Stage := [
  ((15,19),⟨⟨0,(-4500),0,0⟩,[82500,0,0,0,0,0,0],19⟩),
  ((15,33),⟨⟨672865830,(-63835989),0,1201760⟩,[0,0,0,0,34505940,0,0],14165⟩),
  ((15,47),⟨⟨350,(-70),25,1⟩,[0,0,0,0,0,0,0],0⟩),
  ((15,61),⟨⟨350,(-70),25,1⟩,[0,0,0,0,0,0,0],0⟩),
  ((20,26),⟨⟨20097,(-3654),0,77⟩,[0,0,0,0,0,0,16443],2⟩),
  ((20,54),⟨⟨350,(-70),25,1⟩,[0,0,0,0,0,0,0],0⟩),
  ((20,68),⟨⟨(-5950),0,275,(-3)⟩,[0,1400,0,0,0,0,0],0⟩),
  ((25,31),⟨⟨0,(-2548),0,0⟩,[24010,0,10290,0,0,0,0],5⟩),
  ((25,45),⟨⟨0,(-15137913),0,243600⟩,[0,0,0,0,0,0,0],17755⟩),
  ((25,59),⟨⟨0,(-85),50,1⟩,[0,100,0,0,0,0,0],0⟩),
  ((25,73),⟨⟨0,(-315),225,2⟩,[700,0,0,0,0,0,0],0⟩),
  ((30,34),⟨⟨0,(-27405),0,567⟩,[0,0,0,0,0,0,0],25⟩),
  ((30,48),⟨⟨0,(-27405),0,567⟩,[0,0,0,0,0,0,0],25⟩),
  ((30,62),⟨⟨350,(-70),25,1⟩,[0,0,0,0,0,0,0],0⟩),
  ((30,76),⟨⟨0,(-315),225,2⟩,[700,0,0,0,0,0,0],0⟩),
  ((35,35),⟨⟨3973725,(-450660),0,9583⟩,[0,0,0,0,0,0,532875],100⟩),
  ((35,49),⟨⟨600,(-50),0,1⟩,[0,0,0,0,25,0,0],0⟩),
  ((35,63),⟨⟨350,(-70),25,1⟩,[0,0,0,0,0,0,0],0⟩),
  ((35,77),⟨⟨350,(-70),25,1⟩,[0,0,0,0,0,0,0],0⟩)]
private theorem frontier_mixed_609_225_50 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=609) : ¬∃ f : G → ℤ, IsSDS 225 50 f :=
  abelian_short_mixed G 7 87 12 3 5 3 225 50 25 25 1 7 25 2
    types_frontier_mixed_609_225_50 [stage_0_frontier_mixed_609_225_50] ⟨⟨20,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_609_484_309 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=609) : ¬∃ f : G → ℤ, IsSDS 484 309 f :=
  abelian_short_linear G 7 87 12 2 5 3 484 309 25 62 1 7
    ⟨⟨(-3224),114,0,(-1)⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_651_194_19 : List RowType := [(6,18),(6,32),(6,46),(6,60),(6,74),(6,88),(11,15),(11,29),(11,43),(11,57),(11,71),(11,85),(16,16),(16,30),(16,44),(16,58),(16,72),(16,86),(21,21),(21,35),(21,49),(21,63),(21,77),(21,91),(26,30),(26,44),(26,58),(26,72),(26,86)]
private def stage_0_frontier_mixed_651_194_19 : Stage := [
  ((6,18),⟨⟨(-168516),0,0,171⟩,[0,0,0,0,4185,0,11160],10⟩),
  ((6,32),⟨⟨0,(-543057750),0,18876000⟩,[652511250,0,652511250,0,0,0,0],267553⟩),
  ((6,46),⟨⟨231,(-32),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((6,60),⟨⟨231,(-32),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((6,74),⟨⟨231,(-32),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((6,88),⟨⟨(-2037),0,160,(-3)⟩,[0,0,245,0,0,0,0],0⟩),
  ((11,15),⟨⟨(-486446400),(-46679200),0,2470000⟩,[0,0,0,0,583490000,0,0],58349⟩),
  ((16,16),⟨⟨(-2700782),0,0,2842⟩,[0,0,898380,0,0,0,290780],185⟩),
  ((16,30),⟨⟨678342,(-134974),0,4032⟩,[0,0,303800,0,0,0,0],25⟩),
  ((21,21),⟨⟨(-304668),0,0,63⟩,[0,0,0,0,0,0,0],32⟩),
  ((21,35),⟨⟨0,(-1953),0,63⟩,[0,0,0,0,0,0,0],1⟩),
  ((26,30),⟨⟨231,(-32),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((26,44),⟨⟨231,(-32),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((26,58),⟨⟨231,(-32),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((26,72),⟨⟨231,(-32),0,1⟩,[0,0,25,0,0,0,0],0⟩),
  ((26,86),⟨⟨231,(-32),0,1⟩,[0,0,25,0,0,0,0],0⟩)]
private theorem frontier_mixed_651_194_19 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=651) : ¬∃ f : G → ℤ, IsSDS 194 19 f :=
  abelian_short_mixed G 7 93 12 5 5 3 194 19 25 16 1 7 40 3
    types_frontier_mixed_651_194_19 [stage_0_frontier_mixed_651_194_19] ⟨⟨(-29),0,1,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_651_334_159 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=651) : ¬∃ f : G → ℤ, IsSDS 334 159 f :=
  abelian_short_linear G 7 93 12 0 5 3 334 159 25 46 1 7
    ⟨⟨(-102),(-1),3,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_651_341_166 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=651) : ¬∃ f : G → ℤ, IsSDS 341 166 f :=
  abelian_short_linear G 7 93 12 0 5 3 341 166 25 47 1 7
    ⟨⟨(-1106),0,65,(-1)⟩,[140,0,70,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_651_621_446 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=651) : ¬∃ f : G → ℤ, IsSDS 621 446 f :=
  abelian_short_linear G 7 93 12 2 5 3 621 446 25 77 1 7
    ⟨⟨86,0,(-1),0⟩,[5,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_721_289_114 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=721) : ¬∃ f : G → ℤ, IsSDS 289 114 f :=
  abelian_short_linear G 7 103 12 0 5 3 289 114 25 41 1 7
    ⟨⟨(-2),(-1),1,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_721_436_261 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=721) : ¬∃ f : G → ℤ, IsSDS 436 261 f :=
  abelian_short_linear G 7 103 12 0 5 3 436 261 25 62 1 7
    ⟨⟨(-2),(-1),1,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_763_258_83 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=763) : ¬∃ f : G → ℤ, IsSDS 258 83 f :=
  abelian_short_linear G 7 109 12 0 5 3 258 83 25 36 1 7
    ⟨⟨(-46),1,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_763_517_342 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=763) : ¬∃ f : G → ℤ, IsSDS 517 342 f :=
  abelian_short_linear G 7 109 12 0 5 3 517 342 25 73 1 7
    ⟨⟨63,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_777_193_18 : List RowType := [(7,21),(7,35),(7,49),(7,63),(7,77),(12,24),(12,38),(12,52),(12,66),(12,80),(17,19),(17,33),(17,47),(17,61),(17,75),(17,89),(22,34),(22,48),(22,62),(22,76),(22,90),(27,27),(27,41),(27,55),(27,69),(27,83),(27,97)]
private def stage_0_frontier_mixed_777_193_18 : Stage := [
  ((7,21),⟨⟨(-421959618),0,0,(-554894)⟩,[183860400,0,0,0,0,68947650,0],52059⟩),
  ((7,35),⟨⟨264,(-34),0,1⟩,[0,0,0,25,0,0,0],0⟩),
  ((7,49),⟨⟨756,(-161),25,4⟩,[0,0,0,350,0,0,0],0⟩),
  ((7,63),⟨⟨756,(-161),25,4⟩,[0,0,0,350,0,0,0],0⟩),
  ((7,77),⟨⟨0,(-42),15,1⟩,[0,0,0,140,0,0,0],0⟩),
  ((12,24),⟨⟨0,(-552706),0,14168⟩,[1054130,4177670,0,0,0,543900,0],255⟩),
  ((12,66),⟨⟨(-6993),0,340,(-3)⟩,[0,0,0,1400,0,0,0],0⟩),
  ((12,80),⟨⟨(-6993),0,340,(-3)⟩,[0,0,0,1400,0,0,0],0⟩),
  ((17,19),⟨⟨0,(-39886),0,1204⟩,[30044,174566,0,0,0,0,0],17⟩),
  ((17,33),⟨⟨0,(-39886),0,1204⟩,[30044,174566,0,0,0,0,0],17⟩),
  ((17,61),⟨⟨0,(-37),10,1⟩,[0,0,0,150,0,60,0],0⟩),
  ((17,75),⟨⟨0,(-37),10,1⟩,[0,0,0,150,0,60,0],0⟩),
  ((17,89),⟨⟨(-13986),0,675,0⟩,[0,0,0,2800,0,0,0],0⟩),
  ((22,76),⟨⟨(-4536),0,195,(-1)⟩,[490,0,0,1120,0,0,0],0⟩),
  ((22,90),⟨⟨0,(-42),15,1⟩,[0,0,0,140,0,0,0],0⟩),
  ((27,27),⟨⟨0,(-75369),0,2527⟩,[0,0,0,199430,0,0,0],30⟩),
  ((27,41),⟨⟨937062,(-175602),0,4998⟩,[0,0,0,310800,0,0,0],25⟩),
  ((27,55),⟨⟨264,(-34),0,1⟩,[0,0,0,25,0,0,0],0⟩),
  ((27,69),⟨⟨(-756),(-49),50,1⟩,[0,0,0,350,0,0,0],0⟩),
  ((27,83),⟨⟨(-379086),0,18425,0⟩,[0,0,0,75900,0,0,0],0⟩),
  ((27,97),⟨⟨(-13986),0,675,0⟩,[0,0,0,2800,0,0,0],0⟩)]
private theorem frontier_mixed_777_193_18 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=777) : ¬∃ f : G → ℤ, IsSDS 193 18 f :=
  abelian_short_mixed G 7 111 12 5 5 3 193 18 25 17 1 7 16 1
    types_frontier_mixed_777_193_18 [stage_0_frontier_mixed_777_193_18] ⟨⟨(-34),0,1,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_777_200_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=777) : ¬∃ f : G → ℤ, IsSDS 200 25 f :=
  abelian_short_linear G 7 111 12 4 5 3 200 25 25 20 1 7
    ⟨⟨5250,(-875),150,17⟩,[0,0,0,0,1050,0,350],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_777_697_522 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=777) : ¬∃ f : G → ℤ, IsSDS 697 522 f :=
  abelian_short_linear G 7 111 12 2 5 3 697 522 25 91 1 7
    ⟨⟨86,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_777_732_557 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=777) : ¬∃ f : G → ℤ, IsSDS 732 557 f :=
  abelian_short_linear G 7 111 12 2 5 3 732 557 25 94 1 7
    ⟨⟨84,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_917_233_58 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=917) : ¬∃ f : G → ℤ, IsSDS 233 58 f :=
  abelian_short_linear G 7 131 12 0 5 3 233 58 25 33 1 7
    ⟨⟨56,(-17),15,0⟩,[0,0,0,0,0,10,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_917_688_513 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=917) : ¬∃ f : G → ℤ, IsSDS 688 513 f :=
  abelian_short_linear G 7 131 12 0 5 3 688 513 25 98 1 7
    ⟨⟨(-206),(-13),15,0⟩,[10,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_973_193_18 : List RowType := [(9,17),(9,31),(9,45),(9,59),(14,14),(14,28),(14,42),(14,56),(14,70),(19,31),(19,45),(19,59),(19,73),(24,26),(24,40),(24,54),(24,68),(24,82),(29,41),(29,55),(29,69),(29,83)]
private def stage_0_frontier_mixed_973_193_18 : Stage := [
  ((9,17),⟨⟨(-6271958),0,0,(-18172)⟩,[0,0,0,10381910,0,0,0],645⟩),
  ((9,31),⟨⟨(-6271958),0,0,(-18172)⟩,[0,0,0,10381910,0,0,0],645⟩),
  ((9,45),⟨⟨1904,(-217),25,4⟩,[0,0,0,350,0,0,0],0⟩),
  ((9,59),⟨⟨1904,(-217),25,4⟩,[0,0,0,350,0,0,0],0⟩),
  ((14,14),⟨⟨0,0,0,(-1134)⟩,[0,0,0,0,0,0,0],29⟩),
  ((14,28),⟨⟨(-253953),0,0,(-441)⟩,[0,0,0,0,0,0,0],19⟩),
  ((14,42),⟨⟨(-253953),0,0,(-441)⟩,[0,0,0,0,0,0,0],19⟩),
  ((14,70),⟨⟨(-1372),0,95,(-3)⟩,[630,0,0,630,0,0,0],0⟩),
  ((19,31),⟨⟨(-17243506),0,0,(-434)⟩,[0,0,0,0,0,12668460,0],645⟩),
  ((24,26),⟨⟨(-22449056),0,0,13916⟩,[0,0,14964740,5069330,0,0,0],645⟩),
  ((24,40),⟨⟨4454394,(-748237),0,19019⟩,[0,0,0,1459500,0,486500,0],75⟩),
  ((24,82),⟨⟨(-1372),0,95,(-3)⟩,[630,0,0,630,0,0,0],0⟩),
  ((29,41),⟨⟨(-368767),0,0,427⟩,[0,0,0,0,0,0,0],10⟩),
  ((29,55),⟨⟨(-540988),(-55461),0,2527⟩,[0,0,0,0,0,0,0],25⟩),
  ((29,69),⟨⟨574,(-147),25,4⟩,[350,0,0,0,0,0,0],0⟩),
  ((29,83),⟨⟨574,(-147),25,4⟩,[350,0,0,0,0,0,0],0⟩)]
private theorem frontier_mixed_973_193_18 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=973) : ¬∃ f : G → ℤ, IsSDS 193 18 f :=
  abelian_short_mixed G 7 139 12 4 5 3 193 18 25 19 1 7 20 1
    types_frontier_mixed_973_193_18 [stage_0_frontier_mixed_973_193_18] ⟨⟨(-384),0,13,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_973_900_725 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=973) : ¬∃ f : G → ℤ, IsSDS 900 725 f :=
  abelian_short_linear G 7 139 12 2 5 3 900 725 25 120 1 7
    ⟨⟨(-125),1,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_1239_194_19 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1239) : ¬∃ f : G → ℤ, IsSDS 194 19 f :=
  abelian_short_linear G 7 177 12 2 5 3 194 19 25 22 1 7
    ⟨⟨(-264),(-3),10,0⟩,[0,10,0,25,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1239_1125_950 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1239) : ¬∃ f : G → ℤ, IsSDS 1125 950 f :=
  abelian_short_linear G 7 177 12 2 5 3 1125 950 25 155 1 7
    ⟨⟨23200,(-305),0,1⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)



private theorem frontier_mixed_2331_181_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2331) : ¬∃ f : G → ℤ, IsSDS 181 6 f :=
  abelian_short_linear G 7 333 12 4 5 3 181 6 25 17 1 7
    ⟨⟨(-3080),0,88,0⟩,[0,555,0,946,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2331_2274_2099 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2331) : ¬∃ f : G → ℤ, IsSDS 2274 2099 f :=
  abelian_short_linear G 7 333 12 2 5 3 2274 2099 25 316 1 7
    ⟨⟨306,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2919_181_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2919) : ¬∃ f : G → ℤ, IsSDS 181 6 f :=
  abelian_short_linear G 7 417 12 3 5 3 181 6 25 19 1 7
    ⟨⟨(-2674),0,95,(-1)⟩,[210,0,0,210,0,280,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2919_2834_2659 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2919) : ¬∃ f : G → ℤ, IsSDS 2834 2659 f :=
  abelian_short_linear G 7 417 12 2 5 3 2834 2659 25 398 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_3661_184_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3661) : ¬∃ f : G → ℤ, IsSDS 184 9 f :=
  abelian_short_linear G 7 523 12 0 5 3 184 9 25 26 1 7
    ⟨⟨21,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3661_3481_3306 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3661) : ¬∃ f : G → ℤ, IsSDS 3481 3306 f :=
  abelian_short_linear G 7 523 12 0 5 3 3481 3306 25 497 1 7
    ⟨⟨(-502),1,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4123_178_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4123) : ¬∃ f : G → ℤ, IsSDS 178 3 f :=
  abelian_short_linear G 7 589 12 4 5 3 178 3 25 16 1 7
    ⟨⟨(-2080),0,73,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4123_4077_3902 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4123) : ¬∃ f : G → ℤ, IsSDS 4077 3902 f :=
  abelian_short_linear G 7 589 12 2 5 3 4077 3902 25 573 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4291_181_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4291) : ¬∃ f : G → ℤ, IsSDS 181 6 f :=
  abelian_short_linear G 7 613 12 1 5 3 181 6 25 23 1 7
    ⟨⟨(-1344),11,40,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4291_4150_3975 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4291) : ¬∃ f : G → ℤ, IsSDS 4150 3975 f :=
  abelian_short_linear G 7 613 12 1 5 3 4150 3975 25 590 1 7
    ⟨⟨585,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6881_176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6881) : ¬∃ f : G → ℤ, IsSDS 176 1 f :=
  abelian_short_linear G 7 983 12 6 5 3 176 1 25 12 1 7
    ⟨⟨(-4536),0,145,(-11)⟩,[0,0,1680,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6993_177_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6993) : ¬∃ f : G → ℤ, IsSDS 177 2 f :=
  abelian_short_linear G 7 999 12 4 5 3 177 2 25 17 1 7
    ⟨⟨(-117813),0,3652,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6993_6932_6757 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6993) : ¬∃ f : G → ℤ, IsSDS 6932 6757 f :=
  abelian_short_linear G 7 999 12 2 5 3 6932 6757 25 982 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7847_178_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7847) : ¬∃ f : G → ℤ, IsSDS 178 3 f :=
  abelian_short_linear G 7 1121 12 1 5 3 178 3 25 22 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7847_7717_7542 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7847) : ¬∃ f : G → ℤ, IsSDS 7717 7542 f :=
  abelian_short_linear G 7 1121 12 1 5 3 7717 7542 25 1099 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8757_177_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8757) : ¬∃ f : G → ℤ, IsSDS 177 2 f :=
  abelian_short_linear G 7 1251 12 3 5 3 177 2 25 19 1 7
    ⟨⟨9,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8757_8668_8493 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8757) : ¬∃ f : G → ℤ, IsSDS 8668 8493 f :=
  abelian_short_linear G 7 1251 12 2 5 3 8668 8493 25 1232 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10717_177_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10717) : ¬∃ f : G → ℤ, IsSDS 177 2 f :=
  abelian_short_linear G 7 1531 12 2 5 3 177 2 25 21 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10717_10600_10425 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10717) : ¬∃ f : G → ℤ, IsSDS 10600 10425 f :=
  abelian_short_linear G 7 1531 12 2 5 3 10600 10425 25 1510 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12369_176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12369) : ¬∃ f : G → ℤ, IsSDS 176 1 f :=
  abelian_short_linear G 7 1767 12 4 5 3 176 1 25 16 1 7
    ⟨⟨(-224),0,10,(-1)⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12369_12321_12146 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12369) : ¬∃ f : G → ℤ, IsSDS 12321 12146 f :=
  abelian_short_linear G 7 1767 12 2 5 3 12321 12146 25 1751 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12873_177_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12873) : ¬∃ f : G → ℤ, IsSDS 177 2 f :=
  abelian_short_linear G 7 1839 12 1 5 3 177 2 25 23 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12873_12728_12553 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12873) : ¬∃ f : G → ℤ, IsSDS 12728 12553 f :=
  abelian_short_linear G 7 1839 12 1 5 3 12728 12553 25 1816 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15701_176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15701) : ¬∃ f : G → ℤ, IsSDS 176 1 f :=
  abelian_short_linear G 7 2243 12 3 5 3 176 1 25 18 1 7
    ⟨⟨13,(-1),0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15701_15625_15450 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15701) : ¬∃ f : G → ℤ, IsSDS 15625 15450 f :=
  abelian_short_linear G 7 2243 12 2 5 3 15625 15450 25 2225 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23541_176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23541) : ¬∃ f : G → ℤ, IsSDS 176 1 f :=
  abelian_short_linear G 7 3363 12 1 5 3 176 1 25 22 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23541_23409_23234 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23541) : ¬∃ f : G → ℤ, IsSDS 23409 23234 f :=
  abelian_short_linear G 7 3363 12 1 5 3 23409 23234 25 3341 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28049_176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28049) : ¬∃ f : G → ℤ, IsSDS 176 1 f :=
  abelian_short_linear G 7 4007 12 0 5 3 176 1 25 24 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28049_27889_27714 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28049) : ¬∃ f : G → ℤ, IsSDS 27889 27714 f :=
  abelian_short_linear G 7 4007 12 0 5 3 27889 27714 25 3983 1 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_7_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=7*m)
    (hm : 7 < m) (hn : k-l=(7:ℤ)*25) : False := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_7_25
  simp only [keep_7_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=178 := by omega
    rw [hk,hL] at hf
    exact fibre_203_178 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=229 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_259_229_54 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=250 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_259_250_75 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=184 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_329_184_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=206 := by omega
    rw [hk,hL] at hf
    exact reduced_399_206 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=234 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_399_234_59 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=325 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_399_325_150 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=381 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_399_381_206 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=232 := by omega
    rw [hk,hL] at hf
    exact Long413.case_N47790 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=337 := by omega
    rw [hk,hL] at hf
    exact Long413.case_N47853 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=293 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_567_293_118 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=342 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_567_342_167 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=284 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_581_284_109 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=361 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_581_361_186 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_609_176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_609_225_50 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=484 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_609_484_309 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=194 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_651_194_19 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=334 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_651_334_159 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=341 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_651_341_166 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=621 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_651_621_446 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=289 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_721_289_114 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=436 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_721_436_261 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=258 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_763_258_83 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=517 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_763_517_342 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=193 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_777_193_18 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=200 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_777_200_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=697 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_777_697_522 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=732 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_777_732_557 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=233 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_917_233_58 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=688 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_917_688_513 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=193 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_973_193_18 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=900 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_973_900_725 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=178 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_987_178_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=194 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1239_194_19 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1125 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1239_1125_950 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1589_176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1897_177_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=181 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2331_181_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2274 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2331_2274_2099 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=181 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2919_181_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2834 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2919_2834_2659 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2961_176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=184 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3661_184_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3481 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3661_3481_3306 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=178 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4123_178_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4077 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4123_4077_3902 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=181 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4291_181_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4150 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4291_4150_3975 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6881_176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6993_177_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6932 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6993_6932_6757 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=178 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7847_178_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7717 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7847_7717_7542 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8757_177_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=8668 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8757_8668_8493 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10717_177_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=10600 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10717_10600_10425 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12369_176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=12321 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12369_12321_12146 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12873_177_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=12728 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12873_12728_12553 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15701_176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=15625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15701_15625_15450 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23541_176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=23409 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23541_23409_23234 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28049_176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=27889 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28049_27889_27714 G hg ⟨f,hf⟩

end Signed39.Contraction
