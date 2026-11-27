import Signed25Grid43Part0
import Signed25Grid43Part12
import Signed25Grid43Part24
import Signed25Grid43Part36
import Signed25Grid43Part48
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_43_25 : divisorGrid 43 25 322 qInputs_43_25 keep_43_25 := by
  intro d
  fin_cases d
  · exact grid43x25Case0
  · exact grid43x25Case1
  · exact grid43x25Case2
  · exact grid43x25Case3
  · exact grid43x25Case4
  · exact grid43x25Case5
  · exact grid43x25Case6
  · exact grid43x25Case7
  · exact grid43x25Case8
  · exact grid43x25Case9
  · exact grid43x25Case10
  · exact grid43x25Case11
  · exact grid43x25Case12
  · exact grid43x25Case13
  · exact grid43x25Case14
  · exact grid43x25Case15
  · exact grid43x25Case16
  · exact grid43x25Case17
  · exact grid43x25Case18
  · exact grid43x25Case19
  · exact grid43x25Case20
  · exact grid43x25Case21
  · exact grid43x25Case22
  · exact grid43x25Case23
  · exact grid43x25Case24
  · exact grid43x25Case25
  · exact grid43x25Case26
  · exact grid43x25Case27
  · exact grid43x25Case28
  · exact grid43x25Case29
  · exact grid43x25Case30
  · exact grid43x25Case31
  · exact grid43x25Case32
  · exact grid43x25Case33
  · exact grid43x25Case34
  · exact grid43x25Case35
  · exact grid43x25Case36
  · exact grid43x25Case37
  · exact grid43x25Case38
  · exact grid43x25Case39
  · exact grid43x25Case40
  · exact grid43x25Case41
  · exact grid43x25Case42
  · exact grid43x25Case43
  · exact grid43x25Case44
  · exact grid43x25Case45
  · exact grid43x25Case46
  · exact grid43x25Case47
  · exact grid43x25Case48
  · exact grid43x25Case49



private theorem frontier_mixed_2107_1078_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2107) : ¬∃ f : G → ℤ, IsSDS 1078 3 f :=
  abelian_short_linear G 43 49 32 0 5 21 1078 3 25 2 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2451_1150_75 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2451) : ¬∃ f : G → ℤ, IsSDS 1150 75 f :=
  abelian_short_linear G 43 57 32 0 5 21 1150 75 25 10 37 43
    ⟨⟨0,(-1113),253,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2451_1666_591 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2451) : ¬∃ f : G → ℤ, IsSDS 1666 591 f :=
  abelian_short_linear G 43 57 32 0 5 21 1666 591 25 28 37 43
    ⟨⟨(-56),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2451_1709_634 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2451) : ¬∃ f : G → ℤ, IsSDS 1709 634 f :=
  abelian_short_linear G 43 57 32 0 5 21 1709 634 25 29 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2709_1321_246 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2709) : ¬∃ f : G → ℤ, IsSDS 1321 246 f :=
  abelian_short_linear G 43 63 32 0 5 21 1321 246 25 19 37 43
    ⟨⟨(-625),(-112),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2709_1536_461 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2709) : ¬∃ f : G → ℤ, IsSDS 1536 461 f :=
  abelian_short_linear G 43 63 32 0 5 21 1536 461 25 26 37 43
    ⟨⟨6,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2709_2009_934 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2709) : ¬∃ f : G → ℤ, IsSDS 2009 934 f :=
  abelian_short_linear G 43 63 32 0 5 21 2009 934 25 37 37 43
    ⟨⟨22,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2709_2396_1321 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2709) : ¬∃ f : G → ℤ, IsSDS 2396 1321 f :=
  abelian_short_linear G 43 63 32 0 5 21 2396 1321 25 44 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3053_1177_102 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3053) : ¬∃ f : G → ℤ, IsSDS 1177 102 f :=
  abelian_short_linear G 43 71 32 1 5 21 1177 102 25 13 37 43
    ⟨⟨(-1988000),(-78500),78029,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3483_1725_650 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3483) : ¬∃ f : G → ℤ, IsSDS 1725 650 f :=
  abelian_short_linear G 43 81 32 0 5 21 1725 650 25 35 37 43
    ⟨⟨30,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3483_2198_1123 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3483) : ¬∃ f : G → ℤ, IsSDS 2198 1123 f :=
  abelian_short_linear G 43 81 32 0 5 21 2198 1123 25 46 37 43
    ⟨⟨16,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5719_1101_26 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5719) : ¬∃ f : G → ℤ, IsSDS 1101 26 f :=
  abelian_short_linear G 43 133 32 1 5 21 1101 26 25 9 37 43
    ⟨⟨(-37926),(-1462),375,89⟩,[0,0,0,0,8600,0,0,0,0,0,0,0,0,0,6450,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6321_1076_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6321) : ¬∃ f : G → ℤ, IsSDS 1076 1 f :=
  abelian_short_linear G 43 147 32 2 5 21 1076 1 25 2 37 43
    ⟨⟨(-141750),0,2997,0⟩,[0,0,37000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7353_1100_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7353) : ¬∃ f : G → ℤ, IsSDS 1100 25 f :=
  abelian_short_linear G 43 171 32 2 5 21 1100 25 25 10 37 43
    ⟨⟨(-9890000),(-129000),150000,6063⟩,[9890000,0,0,0,0,1290000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7353_1272_197 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7353) : ¬∃ f : G → ℤ, IsSDS 1272 197 f :=
  abelian_short_linear G 43 171 32 0 5 21 1272 197 25 28 37 43
    ⟨⟨(-8250),0,211,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7353_6217_5142 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7353) : ¬∃ f : G → ℤ, IsSDS 6217 5142 f :=
  abelian_short_linear G 43 171 32 0 5 21 6217 5142 25 143 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7697_1225_150 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7697) : ¬∃ f : G → ℤ, IsSDS 1225 150 f :=
  abelian_short_linear G 43 179 32 1 5 21 1225 150 25 25 37 43
    ⟨⟨0,(-4945),750,71⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6450,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6450,0,0,0,0,19350,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7697_6772_5697 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7697) : ¬∃ f : G → ℤ, IsSDS 6772 5697 f :=
  abelian_short_linear G 43 179 32 0 5 21 6772 5697 25 154 37 43
    ⟨⟨(-166000),997,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7783_1077_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7783) : ¬∃ f : G → ℤ, IsSDS 1077 2 f :=
  abelian_short_linear G 43 181 32 2 5 21 1077 2 25 3 37 43
    ⟨⟨(-2322),43,25,2⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8127_1157_82 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8127) : ¬∃ f : G → ℤ, IsSDS 1157 82 f :=
  abelian_short_linear G 43 189 32 2 5 21 1157 82 25 19 37 43
    ⟨⟨0,(-3999),468,61⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,13244,0,0,0,0,0,0,0,0,0,20210,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8127_7650_6575 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8127) : ¬∃ f : G → ℤ, IsSDS 7650 6575 f :=
  abelian_short_linear G 43 189 32 0 5 21 7650 6575 25 170 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9159_1109_34 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9159) : ¬∃ f : G → ℤ, IsSDS 1109 34 f :=
  abelian_short_linear G 43 213 32 2 5 21 1109 34 25 13 37 43
    ⟨⟨(-1128238944),(-85004304),11232585,3684200⟩,[0,0,0,193191600,0,0,0,0,0,0,0,0,0,386383200,0,0,0,0,386383200,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9159_9150_8075 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9159) : ¬∃ f : G → ℤ, IsSDS 9150 8075 f :=
  abelian_short_linear G 43 213 32 0 5 21 9150 8075 25 200 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9761_1184_109 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9761) : ¬∃ f : G → ℤ, IsSDS 1184 109 f :=
  abelian_short_linear G 43 227 32 1 5 21 1184 109 25 24 37 43
    ⟨⟨0,(-30702),1755,703⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,169850,0,0,0,0,96750,0,0,0,0,69230,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9761_8881_7806 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9761) : ¬∃ f : G → ℤ, IsSDS 8881 7806 f :=
  abelian_short_linear G 43 227 32 0 5 21 8881 7806 25 203 37 43
    ⟨⟨178,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9847_1150_75 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9847) : ¬∃ f : G → ℤ, IsSDS 1150 75 f :=
  abelian_short_linear G 43 229 32 2 5 21 1150 75 25 20 37 43
    ⟨⟨0,(-40357500),4380000,1178439⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,107620000,0,0,0,0,80715000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9847_9277_8202 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9847) : ¬∃ f : G → ℤ, IsSDS 9277 8202 f :=
  abelian_short_linear G 43 229 32 0 5 21 9277 8202 25 209 37 43
    ⟨⟨(-229),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14921_1081_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14921) : ¬∃ f : G → ℤ, IsSDS 1081 6 f :=
  abelian_short_linear G 43 347 32 4 5 21 1081 6 25 7 37 43
    ⟨⟨(-39732),(-1978),375,47⟩,[0,0,0,0,0,0,0,2150,0,0,0,0,6450,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_19823_1138_63 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=19823) : ¬∃ f : G → ℤ, IsSDS 1138 63 f :=
  abelian_short_linear G 43 461 32 0 5 21 1138 63 25 26 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_19823_18725_17650 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=19823) : ¬∃ f : G → ℤ, IsSDS 18725 17650 f :=
  abelian_short_linear G 43 461 32 0 5 21 18725 17650 25 435 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_22489_1096_21 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=22489) : ¬∃ f : G → ℤ, IsSDS 1096 21 f :=
  abelian_short_linear G 43 523 32 4 5 21 1096 21 25 16 37 43
    ⟨⟨(-773912925),(-130032000),7316250,6040296⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,262165625,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_22489_22209_21134 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=22489) : ¬∃ f : G → ℤ, IsSDS 22209 21134 f :=
  abelian_short_linear G 43 523 32 0 5 21 22209 21134 25 507 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23091_1125_50 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23091) : ¬∃ f : G → ℤ, IsSDS 1125 50 f :=
  abelian_short_linear G 43 537 32 0 5 21 1125 50 25 25 37 43
    ⟨⟨0,(-3),1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23091_22066_20991 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23091) : ¬∃ f : G → ℤ, IsSDS 22066 20991 f :=
  abelian_short_linear G 43 537 32 0 5 21 22066 20991 25 512 37 43
    ⟨⟨(-537),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23263_1117_42 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23263) : ¬∃ f : G → ℤ, IsSDS 1117 42 f :=
  abelian_short_linear G 43 541 32 1 5 21 1117 42 25 23 37 43
    ⟨⟨(-15000),0,361,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23263_22402_21327 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23263) : ¬∃ f : G → ℤ, IsSDS 22402 21327 f :=
  abelian_short_linear G 43 541 32 0 5 21 22402 21327 25 518 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23951_1109_34 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23951) : ¬∃ f : G → ℤ, IsSDS 1109 34 f :=
  abelian_short_linear G 43 557 32 2 5 21 1109 34 25 21 37 43
    ⟨⟨0,(-17114),155,529⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,73100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23951_23254_22179 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23951) : ¬∃ f : G → ℤ, IsSDS 23254 22179 f :=
  abelian_short_linear G 43 557 32 0 5 21 23254 22179 25 536 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_29541_1100_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=29541) : ¬∃ f : G → ℤ, IsSDS 1100 25 f :=
  abelian_short_linear G 43 687 32 2 5 21 1100 25 25 20 37 43
    ⟨⟨(-67550000),(-48636000),1885000,1527981⟩,[67550000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,67550000,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_29541_28921_27846 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=29541) : ¬∃ f : G → ℤ, IsSDS 28921 27846 f :=
  abelian_short_linear G 43 687 32 0 5 21 28921 27846 25 667 37 43
    ⟨⟨(-687),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_37109_1081_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=37109) : ¬∃ f : G → ℤ, IsSDS 1081 6 f :=
  abelian_short_linear G 43 863 32 7 5 21 1081 6 25 11 37 43
    ⟨⟨(-2494),(-387),25,6⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_44763_1077_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=44763) : ¬∃ f : G → ℤ, IsSDS 1077 2 f :=
  abelian_short_linear G 43 1041 32 9 5 21 1077 2 25 7 37 43
    ⟨⟨(-87469),(-3803),995,0⟩,[0,0,0,0,0,0,0,19015,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_65489_1076_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=65489) : ¬∃ f : G → ℤ, IsSDS 1076 1 f :=
  abelian_short_linear G 43 1523 32 9 5 21 1076 1 25 6 37 43
    ⟨⟨(-25542),(-3311),525,0⟩,[0,0,0,0,0,0,0,0,0,0,0,2150,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_67467_1082_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=67467) : ¬∃ f : G → ℤ, IsSDS 1082 7 f :=
  abelian_short_linear G 43 1569 32 4 5 21 1082 7 25 16 37 43
    ⟨⟨0,0,121,(-317)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_67467_67173_66098 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=67467) : ¬∃ f : G → ℤ, IsSDS 67173 66098 f :=
  abelian_short_linear G 43 1569 32 0 5 21 67173 66098 25 1553 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_69789_1089_14 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=69789) : ¬∃ f : G → ℤ, IsSDS 1089 14 f :=
  abelian_short_linear G 43 1623 32 1 5 21 1089 14 25 23 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_69789_68900_67825 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=69789) : ¬∃ f : G → ℤ, IsSDS 68900 67825 f :=
  abelian_short_linear G 43 1623 32 0 5 21 68900 67825 25 1600 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_111327_1077_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=111327) : ¬∃ f : G → ℤ, IsSDS 1077 2 f :=
  abelian_short_linear G 43 2589 32 7 5 21 1077 2 25 11 37 43
    ⟨⟨(-524170000),(-360718400),13107500,11948797⟩,[0,0,0,0,0,0,140905625,0,0,0,0,0,0,0,0,0,704528125,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_157423_1078_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=157423) : ¬∃ f : G → ℤ, IsSDS 1078 3 f :=
  abelian_short_linear G 43 3661 32 4 5 21 1078 3 25 16 37 43
    ⟨⟨0,0,121,(-357)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_157423_157125_156050 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=157423) : ¬∃ f : G → ℤ, IsSDS 157125 156050 f :=
  abelian_short_linear G 43 3661 32 0 5 21 157125 156050 25 3645 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_162841_1081_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=162841) : ¬∃ f : G → ℤ, IsSDS 1081 6 f :=
  abelian_short_linear G 43 3787 32 1 5 21 1081 6 25 23 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_162841_161944_160869 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=162841) : ¬∃ f : G → ℤ, IsSDS 161944 160869 f :=
  abelian_short_linear G 43 3787 32 0 5 21 161944 160869 25 3764 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_472269_1076_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=472269) : ¬∃ f : G → ℤ, IsSDS 1076 1 f :=
  abelian_short_linear G 43 10983 32 4 5 21 1076 1 25 16 37 43
    ⟨⟨0,(-129),45,(-196)⟩,[0,0,0,0,0,0,0,0,0,0,0,8170,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_472269_471969_470894 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=472269) : ¬∃ f : G → ℤ, IsSDS 471969 470894 f :=
  abelian_short_linear G 43 10983 32 0 5 21 471969 470894 25 10967 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_488523_1077_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=488523) : ¬∃ f : G → ℤ, IsSDS 1077 2 f :=
  abelian_short_linear G 43 11361 32 1 5 21 1077 2 25 23 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_488523_487622_486547 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=488523) : ¬∃ f : G → ℤ, IsSDS 487622 486547 f :=
  abelian_short_linear G 43 11361 32 0 5 21 487622 486547 25 11338 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_598001_1076_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=598001) : ¬∃ f : G → ℤ, IsSDS 1076 1 f :=
  abelian_short_linear G 43 13907 32 3 5 21 1076 1 25 18 37 43
    ⟨⟨8,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_598001_597529_596454 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=598001) : ¬∃ f : G → ℤ, IsSDS 597529 596454 f :=
  abelian_short_linear G 43 13907 32 0 5 21 597529 596454 25 13889 37 43
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_43_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=43*m)
    (hm : 43 < m) (hn : k-l=(43:ℤ)*25) : False := by
  let : Fact (Nat.Prime 43) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_43_25
  simp only [keep_43_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1078 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2107_1078_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1150 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2451_1150_75 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1666 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2451_1666_591 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1709 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2451_1709_634 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1321 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2709_1321_246 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1536 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2709_1536_461 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2009 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2709_2009_934 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2396 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2709_2396_1321 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3053_1177_102 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1725 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3483_1725_650 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2198 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3483_2198_1123 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1101 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5719_1101_26 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1076 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6321_1076_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1100 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7353_1100_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1272 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7353_1272_197 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6217 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7353_6217_5142 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7697_1225_150 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6772 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7697_6772_5697 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1077 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7783_1077_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1157 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8127_1157_82 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7650 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8127_7650_6575 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1109 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9159_1109_34 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=9150 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9159_9150_8075 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1184 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9761_1184_109 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=8881 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9761_8881_7806 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1150 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9847_1150_75 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=9277 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9847_9277_8202 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1081 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14921_1081_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1138 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_19823_1138_63 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=18725 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_19823_18725_17650 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1096 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_22489_1096_21 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=22209 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_22489_22209_21134 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1125 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23091_1125_50 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=22066 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23091_22066_20991 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1117 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23263_1117_42 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=22402 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23263_22402_21327 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1109 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23951_1109_34 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=23254 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23951_23254_22179 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1100 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_29541_1100_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=28921 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_29541_28921_27846 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1081 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_37109_1081_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1077 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_44763_1077_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1076 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_65489_1076_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1082 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_67467_1082_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=67173 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_67467_67173_66098 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1089 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_69789_1089_14 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=68900 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_69789_68900_67825 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1077 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_111327_1077_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1078 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_157423_1078_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=157125 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_157423_157125_156050 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1081 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_162841_1081_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=161944 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_162841_161944_160869 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1076 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_472269_1076_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=471969 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_472269_471969_470894 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1077 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_488523_1077_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=487622 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_488523_487622_486547 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1076 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_598001_1076_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=597529 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_598001_597529_596454 G hg ⟨f,hf⟩

end Signed39.Contraction
