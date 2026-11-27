import Signed25Grid31Part0
import Signed25Grid31Part12
import Signed25Grid31Part24
import Signed25Grid31Part36
import Signed25Grid31Part48
import Signed3875Anchors
import SignedReducedPrimeCases
import Signed25Case3069W776
import Signed25Case21545W785
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_31_25 : divisorGrid 31 25 273 qInputs_31_25 keep_31_25 := by
  intro d
  fin_cases d
  · exact grid31x25Case0
  · exact grid31x25Case1
  · exact grid31x25Case2
  · exact grid31x25Case3
  · exact grid31x25Case4
  · exact grid31x25Case5
  · exact grid31x25Case6
  · exact grid31x25Case7
  · exact grid31x25Case8
  · exact grid31x25Case9
  · exact grid31x25Case10
  · exact grid31x25Case11
  · exact grid31x25Case12
  · exact grid31x25Case13
  · exact grid31x25Case14
  · exact grid31x25Case15
  · exact grid31x25Case16
  · exact grid31x25Case17
  · exact grid31x25Case18
  · exact grid31x25Case19
  · exact grid31x25Case20
  · exact grid31x25Case21
  · exact grid31x25Case22
  · exact grid31x25Case23
  · exact grid31x25Case24
  · exact grid31x25Case25
  · exact grid31x25Case26
  · exact grid31x25Case27
  · exact grid31x25Case28
  · exact grid31x25Case29
  · exact grid31x25Case30
  · exact grid31x25Case31
  · exact grid31x25Case32
  · exact grid31x25Case33
  · exact grid31x25Case34
  · exact grid31x25Case35
  · exact grid31x25Case36
  · exact grid31x25Case37
  · exact grid31x25Case38
  · exact grid31x25Case39
  · exact grid31x25Case40
  · exact grid31x25Case41
  · exact grid31x25Case42
  · exact grid31x25Case43
  · exact grid31x25Case44
  · exact grid31x25Case45
  · exact grid31x25Case46
  · exact grid31x25Case47
  · exact grid31x25Case48
  · exact grid31x25Case49



private theorem frontier_mixed_1023_778_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1023) : ¬∃ f : G → ℤ, IsSDS 778 3 f :=
  abelian_short_linear G 31 33 27 0 1 0 778 3 25 2 18 29
    ⟨⟨0,0,(-2),1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1023_933_158 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1023) : ¬∃ f : G → ℤ, IsSDS 933 158 f :=
  abelian_short_linear G 31 33 27 0 1 0 933 158 25 13 18 29
    ⟨⟨0,(-124),25,3⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1333_1008_233 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1333) : ¬∃ f : G → ℤ, IsSDS 1008 233 f :=
  abelian_short_linear G 31 43 27 0 1 0 1008 233 25 18 18 29
    ⟨⟨0,(-651),221,10⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1333_1225_450 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1333) : ¬∃ f : G → ℤ, IsSDS 1225 450 f :=
  abelian_short_linear G 31 43 27 0 1 0 1225 450 25 25 18 29
    ⟨⟨106640,837,(-3240),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1395_1050_275 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1395) : ¬∃ f : G → ℤ, IsSDS 1050 275 f :=
  abelian_short_linear G 31 45 27 0 1 0 1050 275 25 20 18 29
    ⟨⟨405,(-54),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,68,0,0,0,0,203,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1395_1205_430 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1395) : ¬∃ f : G → ℤ, IsSDS 1205 430 f :=
  abelian_short_linear G 31 45 27 0 1 0 1205 430 25 25 18 29
    ⟨⟨0,(-2242323),434000,40185⟩,[0,0,0,0,0,0,0,0,0,0,0,5481234,0,0,0,0,9965880,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1705_1000_225 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1705) : ¬∃ f : G → ℤ, IsSDS 1000 225 f :=
  abelian_short_linear G 31 55 27 1 1 0 1000 225 25 20 18 29
    ⟨⟨0,(-2891184),621760,54405⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,8673552,0,0,0,0,12287532,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1705_1465_690 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1705) : ¬∃ f : G → ℤ, IsSDS 1465 690 f :=
  abelian_short_linear G 31 55 27 0 1 0 1465 690 25 35 18 29
    ⟨⟨880,(-71),0,1⟩,[0,0,0,0,0,380,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2139_829_54 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2139) : ¬∃ f : G → ℤ, IsSDS 829 54 f :=
  abelian_short_linear G 31 69 27 1 1 0 829 54 25 11 18 29
    ⟨⟨0,(-310),75,7⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,372,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2139_1294_519 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2139) : ¬∃ f : G → ℤ, IsSDS 1294 519 f :=
  abelian_short_linear G 31 69 27 1 1 0 1294 519 25 34 18 29
    ⟨⟨0,0,841,(-67)⟩,[0,0,16616,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4030,0,5952,10478,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2139_1325_550 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2139) : ¬∃ f : G → ℤ, IsSDS 1325 550 f :=
  abelian_short_linear G 31 69 27 0 1 0 1325 550 25 35 18 29
    ⟨⟨0,0,841,(-67)⟩,[0,0,16616,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4030,0,5952,10478,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2325_785_10 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2325) : ¬∃ f : G → ℤ, IsSDS 785 10 f :=
  abelian_short_linear G 31 75 27 1 1 0 785 10 25 5 18 29
    ⟨⟨(-186),(-31),5,2⟩,[186,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2325_816_41 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2325) : ¬∃ f : G → ℤ, IsSDS 816 41 f :=
  abelian_short_linear G 31 75 27 1 1 0 816 41 25 10 18 29
    ⟨⟨0,(-1412400),164031,56210⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2636480,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2325_940_165 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2325) : ¬∃ f : G → ℤ, IsSDS 940 165 f :=
  abelian_short_linear G 31 75 27 1 1 0 940 165 25 20 18 29
    ⟨⟨0,(-3911318361),1006176875,80657775⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7723616004,0,0,0,0,0,4752994464,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2325_1033_258 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2325) : ¬∃ f : G → ℤ, IsSDS 1033 258 f :=
  abelian_short_linear G 31 75 27 1 1 0 1033 258 25 25 18 29
    ⟨⟨0,(-8990),2448,167⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,17856,0,0,0,0,0,14136,0,0,0,0,0,8184,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2325_1281_506 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2325) : ¬∃ f : G → ℤ, IsSDS 1281 506 f :=
  abelian_short_linear G 31 75 27 1 1 0 1281 506 25 35 18 29
    ⟨⟨0,(-17887),7462,201⟩,[0,0,0,32550,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2325_1436_661 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2325) : ¬∃ f : G → ℤ, IsSDS 1436 661 f :=
  abelian_short_linear G 31 75 27 1 1 0 1436 661 25 40 18 29
    ⟨⟨0,0,512,(-37)⟩,[0,0,0,19220,0,0,0,0,0,0,35061,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5456,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2325_1808_1033 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2325) : ¬∃ f : G → ℤ, IsSDS 1808 1033 f :=
  abelian_short_linear G 31 75 27 0 1 0 1808 1033 25 50 18 29
    ⟨⟨2100,(-103),0,1⟩,[0,172,0,246,0,0,0,0,0,0,442,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2325_2025_1250 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2325) : ¬∃ f : G → ℤ, IsSDS 2025 1250 f :=
  abelian_short_linear G 31 75 27 0 1 0 2025 1250 25 55 18 29
    ⟨⟨3075,(-116),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2449_841_66 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2449) : ¬∃ f : G → ℤ, IsSDS 841 66 f :=
  abelian_short_linear G 31 79 27 1 1 0 841 66 25 13 18 29
    ⟨⟨0,(-9083),1155,284⟩,[0,0,0,0,0,0,0,0,0,0,9300,0,0,0,16058,6510,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2511_821_46 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2511) : ¬∃ f : G → ℤ, IsSDS 821 46 f :=
  abelian_short_linear G 31 81 27 1 1 0 821 46 25 11 18 29
    ⟨⟨0,(-18073),2958,479⟩,[0,0,0,0,0,0,0,0,7440,0,0,25482,0,0,0,12462,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2573_793_18 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2573) : ¬∃ f : G → ℤ, IsSDS 793 18 f :=
  abelian_short_linear G 31 83 27 1 1 0 793 18 25 7 18 29
    ⟨⟨0,(-93),9,4⟩,[0,0,0,0,0,0,0,0,0,0,62,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_3069_900_125 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3069) : ¬∃ f : G → ℤ, IsSDS 900 125 f :=
  abelian_short_linear G 31 99 27 1 1 0 900 125 25 20 18 29
    ⟨⟨0,(-4960),1309,97⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,186,0,0,0,0,14942,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3069_2729_1954 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3069) : ¬∃ f : G → ℤ, IsSDS 2729 1954 f :=
  abelian_short_linear G 31 99 27 0 1 0 2729 1954 25 79 18 29
    ⟨⟨7326,(-173),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3131_1109_334 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3131) : ¬∃ f : G → ℤ, IsSDS 1109 334 f :=
  abelian_short_linear G 31 101 27 1 1 0 1109 334 25 33 18 29
    ⟨⟨0,(-31837),9675,484⟩,[0,0,0,0,0,0,21948,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,61504,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3131_2194_1419 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3131) : ¬∃ f : G → ℤ, IsSDS 2194 1419 f :=
  abelian_short_linear G 31 101 27 0 1 0 2194 1419 25 68 18 29
    ⟨⟨0,0,3721,(-97)⟩,[0,24056,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,22382,0,0,0,88164,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3565_1105_330 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3565) : ¬∃ f : G → ℤ, IsSDS 1105 330 f :=
  abelian_short_linear G 31 115 27 0 1 0 1105 330 25 35 18 29
    ⟨⟨(-52),0,1,0⟩,[0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3565_2500_1725 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3565) : ¬∃ f : G → ℤ, IsSDS 2500 1725 f :=
  abelian_short_linear G 31 115 27 0 1 0 2500 1725 25 80 18 29
    ⟨⟨79,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3751_1021_246 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3751) : ¬∃ f : G → ℤ, IsSDS 1021 246 f :=
  abelian_short_linear G 31 121 27 0 1 0 1021 246 25 31 18 29
    ⟨⟨(-195424),(-11067),6579,178⟩,[0,0,0,0,0,0,0,0,20770,0,0,0,0,0,65472,0,0,0,0,45384,0,0,0,20274,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3751_2850_2075 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3751) : ¬∃ f : G → ℤ, IsSDS 2850 2075 f :=
  abelian_short_linear G 31 121 27 0 1 0 2850 2075 25 90 18 29
    ⟨⟨6561,0,0,(-1)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,664,835,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3875_874_99 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3875) : ¬∃ f : G → ℤ, IsSDS 874 99 f :=
  abelian_short_linear G 31 125 27 2 1 0 874 99 25 20 18 29
    ⟨⟨0,(-712659992),224258254,10106279⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1334440756,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3875_998_223 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3875) : ¬∃ f : G → ℤ, IsSDS 998 223 f :=
  abelian_short_linear G 31 125 27 1 1 0 998 223 25 30 18 29
    ⟨⟨0,(-2635),867,32⟩,[0,0,0,17918,0,4836,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7068,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3875_3013_2238 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3875) : ¬∃ f : G → ℤ, IsSDS 3013 2238 f :=
  abelian_short_linear G 31 125 27 0 1 0 3013 2238 25 95 18 29
    ⟨⟨0,0,3872,(-59)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,112995,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3875_3509_2734 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3875) : ¬∃ f : G → ℤ, IsSDS 3509 2734 f :=
  abelian_short_linear G 31 125 27 0 1 0 3509 2734 25 105 18 29
    ⟨⟨11000,(-213),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3999_925_150 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3999) : ¬∃ f : G → ℤ, IsSDS 925 150 f :=
  abelian_short_linear G 31 129 27 2 1 0 925 150 25 25 18 29
    ⟨⟨0,(-930),225,17⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,558,0,0,0,0,4588,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3999_3374_2599 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3999) : ¬∃ f : G → ℤ, IsSDS 3374 2599 f :=
  abelian_short_linear G 31 129 27 0 1 0 3374 2599 25 104 18 29
    ⟨⟨(-23994),0,315,(-1)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,310,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4309_825_50 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4309) : ¬∃ f : G → ℤ, IsSDS 825 50 f :=
  abelian_short_linear G 31 139 27 2 1 0 825 50 25 15 18 29
    ⟨⟨0,(-868),209,15⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,434,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4309_4204_3429 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4309) : ¬∃ f : G → ℤ, IsSDS 4204 3429 f :=
  abelian_short_linear G 31 139 27 0 1 0 4204 3429 25 124 18 29
    ⟨⟨1807,8,(-21),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5115_850_75 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5115) : ¬∃ f : G → ℤ, IsSDS 850 75 f :=
  abelian_short_linear G 31 165 27 2 1 0 850 75 25 20 18 29
    ⟨⟨0,(-3186924),385515,94240⟩,[0,0,0,0,0,0,0,2655770,0,0,0,0,0,5842694,0,0,0,2655770,0,0,0,0,0,0,0,2655770,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5115_4725_3950 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5115) : ¬∃ f : G → ℤ, IsSDS 4725 3950 f :=
  abelian_short_linear G 31 165 27 0 1 0 4725 3950 25 145 18 29
    ⟨⟨327360,(-4743),119,16⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6417_793_18 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6417) : ¬∃ f : G → ℤ, IsSDS 793 18 f :=
  abelian_short_linear G 31 207 27 3 1 0 793 18 25 11 18 29
    ⟨⟨0,(-923000),68700,48777⟩,[0,0,0,0,0,0,0,0,0,0,0,0,852000,0,0,532500,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6665_865_90 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6665) : ¬∃ f : G → ℤ, IsSDS 865 90 f :=
  abelian_short_linear G 31 215 27 1 1 0 865 90 25 25 18 29
    ⟨⟨0,(-17143),3480,283⟩,[0,0,0,0,0,0,0,0,0,2604,0,0,0,0,0,0,0,11284,0,0,0,0,3534,32302,0,0,136090,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6665_5980_5205 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6665) : ¬∃ f : G → ℤ, IsSDS 5980 5205 f :=
  abelian_short_linear G 31 215 27 0 1 0 5980 5205 25 190 18 29
    ⟨⟨(-10590556),(-44505),96495,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6975_830_55 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6975) : ¬∃ f : G → ℤ, IsSDS 830 55 f :=
  abelian_short_linear G 31 225 27 3 1 0 830 55 25 20 18 29
    ⟨⟨0,(-2728),425,67⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6510,2666,0,0,0,4650,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6975_861_86 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6975) : ¬∃ f : G → ℤ, IsSDS 861 86 f :=
  abelian_short_linear G 31 225 27 1 1 0 861 86 25 25 18 29
    ⟨⟨0,(-2418),540,41⟩,[0,0,0,0,0,0,5797,0,0,0,0,0,0,0,0,0,0,0,0,4681,4960,0,0,0,0,7285,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6975_6286_5511 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6975) : ¬∃ f : G → ℤ, IsSDS 6286 5511 f :=
  abelian_short_linear G 31 225 27 0 1 0 6286 5511 25 200 18 29
    ⟨⟨(-225829114),(-1944243),2948805,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6975_6565_5790 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6975) : ¬∃ f : G → ℤ, IsSDS 6565 5790 f :=
  abelian_short_linear G 31 225 27 0 1 0 6565 5790 25 205 18 29
    ⟨⟨42975,(-416),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7347_797_22 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7347) : ¬∃ f : G → ℤ, IsSDS 797 22 f :=
  abelian_short_linear G 31 237 27 4 1 0 797 22 25 13 18 29
    ⟨⟨(-3286),(-713),88,39⟩,[3286,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,310,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7347_7338_6563 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7347) : ¬∃ f : G → ℤ, IsSDS 7338 6563 f :=
  abelian_short_linear G 31 237 27 0 1 0 7338 6563 25 224 18 29
    ⟨⟨3555,2,(-17),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7719_781_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7719) : ¬∃ f : G → ℤ, IsSDS 781 6 f :=
  abelian_short_linear G 31 249 27 4 1 0 781 6 25 7 18 29
    ⟨⟨(-15624),(-279),272,7⟩,[15624,0,0,0,0,0,0,3906,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8525_820_45 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8525) : ¬∃ f : G → ℤ, IsSDS 820 45 f :=
  abelian_short_linear G 31 275 27 3 1 0 820 45 25 20 18 29
    ⟨⟨0,(-1946149),426335,41230⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,406658,0,0,0,0,0,0,0,0,0,0,290470,2265666,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8525_8105_7330 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8525) : ¬∃ f : G → ℤ, IsSDS 8105 7330 f :=
  abelian_short_linear G 31 275 27 0 1 0 8105 7330 25 255 18 29
    ⟨⟨(-275),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11625_777_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11625) : ¬∃ f : G → ℤ, IsSDS 777 2 f :=
  abelian_short_linear G 31 375 27 6 1 0 777 2 25 5 18 29
    ⟨⟨(-5766),(-31),114,(-7)⟩,[5766,0,0,0,0,0,0,0,0,0,620,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11625_808_33 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11625) : ¬∃ f : G → ℤ, IsSDS 808 33 f :=
  abelian_short_linear G 31 375 27 3 1 0 808 33 25 20 18 29
    ⟨⟨0,(-25451),5355,478⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,56916,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11625_11193_10418 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11625) : ¬∃ f : G → ℤ, IsSDS 11193 10418 f :=
  abelian_short_linear G 31 375 27 0 1 0 11193 10418 25 355 18 29
    ⟨⟨(-375),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11997_825_50 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11997) : ¬∃ f : G → ℤ, IsSDS 825 50 f :=
  abelian_short_linear G 31 387 27 0 1 0 825 50 25 25 18 29
    ⟨⟨0,(-864),533,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11997_11272_10497 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11997) : ¬∃ f : G → ℤ, IsSDS 11272 10497 f :=
  abelian_short_linear G 31 387 27 0 1 0 11272 10497 25 362 18 29
    ⟨⟨(-387),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15345_800_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15345) : ¬∃ f : G → ℤ, IsSDS 800 25 f :=
  abelian_short_linear G 31 495 27 2 1 0 800 25 25 20 18 29
    ⟨⟨0,(-1000),41,41⟩,[0,0,0,0,0,200,0,0,0,0,400,0,0,0,0,600,0,200,0,0,800,0,400,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15345_14905_14130 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15345) : ¬∃ f : G → ℤ, IsSDS 14905 14130 f :=
  abelian_short_linear G 31 495 27 0 1 0 14905 14130 25 475 18 29
    ⟨⟨(-495),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_19251_781_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=19251) : ¬∃ f : G → ℤ, IsSDS 781 6 f :=
  abelian_short_linear G 31 621 27 7 1 0 781 6 25 11 18 29
    ⟨⟨(-12738),(-1009),186,11⟩,[12738,2018,2436,2460,2090,1326,168,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_19995_805_30 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=19995) : ¬∃ f : G → ℤ, IsSDS 805 30 f :=
  abelian_short_linear G 31 645 27 0 1 0 805 30 25 25 18 29
    ⟨⟨0,(-893),726,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_19995_19250_18475 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=19995) : ¬∃ f : G → ℤ, IsSDS 19250 18475 f :=
  abelian_short_linear G 31 645 27 0 1 0 19250 18475 25 620 18 29
    ⟨⟨(-2554),(-9),13,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20243_778_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20243) : ¬∃ f : G → ℤ, IsSDS 778 3 f :=
  abelian_short_linear G 31 653 27 8 1 0 778 3 25 8 18 29
    ⟨⟨(-1536),(-81),31,(-2)⟩,[1536,162,0,216,0,162,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_21545_21400_20625 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=21545) : ¬∃ f : G → ℤ, IsSDS 21400 20625 f :=
  abelian_short_linear G 31 695 27 0 1 0 21400 20625 25 680 18 29
    ⟨⟨(-695),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23157_777_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23157) : ¬∃ f : G → ℤ, IsSDS 777 2 f :=
  abelian_short_linear G 31 747 27 9 1 0 777 2 25 7 18 29
    ⟨⟨(-1252),(-11),17,(-2)⟩,[1252,0,0,198,0,0,132,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,132,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_25575_790_15 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=25575) : ¬∃ f : G → ℤ, IsSDS 790 15 f :=
  abelian_short_linear G 31 825 27 2 1 0 790 15 25 20 18 29
    ⟨⟨(-664),(-676),27,17⟩,[664,0,4,676,342,676,4,0,664,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_25575_25125_24350 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=25575) : ¬∃ f : G → ℤ, IsSDS 25125 24350 f :=
  abelian_short_linear G 31 825 27 0 1 0 25125 24350 25 805 18 29
    ⟨⟨(-825),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_26939_781_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=26939) : ¬∃ f : G → ℤ, IsSDS 781 6 f :=
  abelian_short_linear G 31 869 27 6 1 0 781 6 25 13 18 29
    ⟨⟨0,(-34441),1800,649⟩,[0,0,0,0,0,0,6882,9486,7192,0,0,0,0,33852,2170,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_26939_26914_26139 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=26939) : ¬∃ f : G → ℤ, IsSDS 26914 26139 f :=
  abelian_short_linear G 31 869 27 0 1 0 26914 26139 25 856 18 29
    ⟨⟨(-869),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_33325_793_18 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=33325) : ¬∃ f : G → ℤ, IsSDS 793 18 f :=
  abelian_short_linear G 31 1075 27 0 1 0 793 18 25 25 18 29
    ⟨⟨0,(-103),76,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_33325_32568_31793 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=33325) : ¬∃ f : G → ℤ, IsSDS 32568 31793 f :=
  abelian_short_linear G 31 1075 27 0 1 0 32568 31793 25 1050 18 29
    ⟨⟨(-1075),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_33821_776_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=33821) : ¬∃ f : G → ℤ, IsSDS 776 1 f :=
  abelian_short_linear G 31 1091 27 9 1 0 776 1 25 6 18 29
    ⟨⟨(-158402552),(-4581892),3325800,(-390425)⟩,[158402552,0,29455020,0,36655136,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11127452,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_34875_786_11 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=34875) : ¬∃ f : G → ℤ, IsSDS 786 11 f :=
  abelian_short_linear G 31 1125 27 2 1 0 786 11 25 20 18 29
    ⟨⟨(-88443),(-15314),1056,265⟩,[88443,30628,22971,0,27187,39060,0,16864,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_34875_34421_33646 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=34875) : ¬∃ f : G → ℤ, IsSDS 34421 33646 f :=
  abelian_short_linear G 31 1125 27 0 1 0 34421 33646 25 1105 18 29
    ⟨⟨(-1125),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_42625_784_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=42625) : ¬∃ f : G → ℤ, IsSDS 784 9 f :=
  abelian_short_linear G 31 1375 27 2 1 0 784 9 25 20 18 29
    ⟨⟨0,(-31),3,(-20)⟩,[0,0,0,0,0,310,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_42625_42169_41394 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=42625) : ¬∃ f : G → ℤ, IsSDS 42169 41394 f :=
  abelian_short_linear G 31 1375 27 0 1 0 42169 41394 25 1355 18 29
    ⟨⟨(-1375),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_57753_777_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=57753) : ¬∃ f : G → ℤ, IsSDS 777 2 f :=
  abelian_short_linear G 31 1863 27 7 1 0 777 2 25 11 18 29
    ⟨⟨(-138136),(-1302),1653,(-365)⟩,[138136,2604,3348,37882,3720,3348,0,1488,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,30070,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_59985_785_10 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=59985) : ¬∃ f : G → ℤ, IsSDS 785 10 f :=
  abelian_short_linear G 31 1935 27 0 1 0 785 10 25 25 18 29
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_59985_59220_58445 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=59985) : ¬∃ f : G → ℤ, IsSDS 59220 58445 f :=
  abelian_short_linear G 31 1935 27 0 1 0 59220 58445 25 1910 18 29
    ⟨⟨(-1935),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_60729_776_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=60729) : ¬∃ f : G → ℤ, IsSDS 776 1 f :=
  abelian_short_linear G 31 1959 27 8 1 0 776 1 25 8 18 29
    ⟨⟨(-66464),(-2790),1330,(-201)⟩,[66464,0,16988,0,22320,4309,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5828,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_76725_780_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=76725) : ¬∃ f : G → ℤ, IsSDS 780 5 f :=
  abelian_short_linear G 31 2475 27 2 1 0 780 5 25 20 18 29
    ⟨⟨1,0,0,(-1)⟩,[0,0,3,8,15,24,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,35,24,15,8,3,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_76725_76265_75490 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=76725) : ¬∃ f : G → ℤ, IsSDS 76265 75490 f :=
  abelian_short_linear G 31 2475 27 0 1 0 76265 75490 25 2455 18 29
    ⟨⟨(-2475),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_80817_777_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=80817) : ¬∃ f : G → ℤ, IsSDS 777 2 f :=
  abelian_short_linear G 31 2607 27 6 1 0 777 2 25 13 18 29
    ⟨⟨(-3166862),0,38353,(-16436)⟩,[3166862,0,10958,821850,54790,87664,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,87664,54790,821850,10958,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_80817_80788_80013 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=80817) : ¬∃ f : G → ℤ, IsSDS 80788 80013 f :=
  abelian_short_linear G 31 2607 27 0 1 0 80788 80013 25 2594 18 29
    ⟨⟨(-2607),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_99975_781_6 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=99975) : ¬∃ f : G → ℤ, IsSDS 781 6 f :=
  abelian_short_linear G 31 3225 27 0 1 0 781 6 25 25 18 29
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_99975_99206_98431 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=99975) : ¬∃ f : G → ℤ, IsSDS 99206 98431 f :=
  abelian_short_linear G 31 3225 27 0 1 0 99206 98431 25 3200 18 29
    ⟨⟨(-3225),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_107725_777_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=107725) : ¬∃ f : G → ℤ, IsSDS 777 2 f :=
  abelian_short_linear G 31 3475 27 5 1 0 777 2 25 15 18 29
    ⟨⟨0,0,6867,(-6220)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_107725_107572_106797 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=107725) : ¬∃ f : G → ℤ, IsSDS 107572 106797 f :=
  abelian_short_linear G 31 3475 27 0 1 0 107572 106797 25 3460 18 29
    ⟨⟨(-3475),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_127875_778_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=127875) : ¬∃ f : G → ℤ, IsSDS 778 3 f :=
  abelian_short_linear G 31 4125 27 2 1 0 778 3 25 20 18 29
    ⟨⟨0,0,4,(-33)⟩,[0,0,0,0,0,341,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,341,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_127875_127413_126638 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=127875) : ¬∃ f : G → ℤ, IsSDS 127413 126638 f :=
  abelian_short_linear G 31 4125 27 0 1 0 127413 126638 25 4105 18 29
    ⟨⟨(-4125),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_211513_777_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=211513) : ¬∃ f : G → ℤ, IsSDS 777 2 f :=
  abelian_short_linear G 31 6823 27 2 1 0 777 2 25 21 18 29
    ⟨⟨3,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_211513_210988_210213 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=211513) : ¬∃ f : G → ℤ, IsSDS 210988 210213 f :=
  abelian_short_linear G 31 6823 27 0 1 0 210988 210213 25 6802 18 29
    ⟨⟨(-6823),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_299925_777_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=299925) : ¬∃ f : G → ℤ, IsSDS 777 2 f :=
  abelian_short_linear G 31 9675 27 0 1 0 777 2 25 25 18 29
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_299925_299152_298377 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=299925) : ¬∃ f : G → ℤ, IsSDS 299152 298377 f :=
  abelian_short_linear G 31 9675 27 0 1 0 299152 298377 25 9650 18 29
    ⟨⟨(-9675),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_383625_776_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=383625) : ¬∃ f : G → ℤ, IsSDS 776 1 f :=
  abelian_short_linear G 31 12375 27 2 1 0 776 1 25 20 18 29
    ⟨⟨0,0,8,(-53)⟩,[0,0,0,0,0,341,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,341,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_383625_383161_382386 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=383625) : ¬∃ f : G → ℤ, IsSDS 383161 382386 f :=
  abelian_short_linear G 31 12375 27 0 1 0 383161 382386 25 12355 18 29
    ⟨⟨(-12375),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_31_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=31*m)
    (hm : 31 < m) (hn : k-l=(31:ℤ)*25) : False := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_31_25
  simp only [keep_31_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=778 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1023_778_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=933 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1023_933_158 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1008 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1333_1008_233 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1333_1225_450 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1050 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1395_1050_275 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1205 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1395_1205_430 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1000 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1705_1000_225 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1465 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1705_1465_690 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=829 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2139_829_54 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1294 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2139_1294_519 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1325 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2139_1325_550 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=785 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2325_785_10 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=816 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2325_816_41 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=940 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2325_940_165 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1033 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2325_1033_258 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1281 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2325_1281_506 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1436 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2325_1436_661 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1808 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2325_1808_1033 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2325_2025_1250 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=841 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2449_841_66 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=821 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2511_821_46 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=793 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2573_793_18 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=776 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3069_776_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=900 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3069_900_125 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2729 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3069_2729_1954 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1109 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3131_1109_334 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2194 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3131_2194_1419 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1105 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3565_1105_330 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2500 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3565_2500_1725 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1021 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3751_1021_246 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2850 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3751_2850_2075 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=781 := by omega
    rw [hk,hL] at hf
    exact reduced_3875_781 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=874 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3875_874_99 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=998 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3875_998_223 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3013 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3875_3013_2238 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3509 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3875_3509_2734 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=777 := by omega
    rw [hk,hL] at hf
    exact reduced_3937_777 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=925 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3999_925_150 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3374 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3999_3374_2599 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=825 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4309_825_50 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4204 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4309_4204_3429 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=850 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5115_850_75 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4725 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5115_4725_3950 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=793 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6417_793_18 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=865 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6665_865_90 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5980 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6665_5980_5205 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=830 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6975_830_55 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=861 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6975_861_86 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6286 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6975_6286_5511 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6565 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6975_6565_5790 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=797 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7347_797_22 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7338 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7347_7338_6563 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=781 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7719_781_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=820 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8525_820_45 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=8105 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8525_8105_7330 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=777 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11625_777_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=808 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11625_808_33 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=11193 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11625_11193_10418 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=825 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11997_825_50 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=11272 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11997_11272_10497 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=800 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15345_800_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=14905 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15345_14905_14130 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=781 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_19251_781_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=805 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_19995_805_30 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=19250 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_19995_19250_18475 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=778 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20243_778_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=785 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_21545_785_10 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=21400 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_21545_21400_20625 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=777 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23157_777_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=790 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_25575_790_15 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=25125 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_25575_25125_24350 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=781 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_26939_781_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=26914 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_26939_26914_26139 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=793 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_33325_793_18 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=32568 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_33325_32568_31793 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=776 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_33821_776_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=786 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_34875_786_11 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=34421 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_34875_34421_33646 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=784 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_42625_784_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=42169 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_42625_42169_41394 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=777 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_57753_777_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=785 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_59985_785_10 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=59220 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_59985_59220_58445 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=776 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_60729_776_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=780 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_76725_780_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=76265 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_76725_76265_75490 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=777 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_80817_777_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=80788 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_80817_80788_80013 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=781 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_99975_781_6 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=99206 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_99975_99206_98431 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=777 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_107725_777_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=107572 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_107725_107572_106797 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=778 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_127875_778_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=127413 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_127875_127413_126638 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=777 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_211513_777_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=210988 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_211513_210988_210213 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=777 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_299925_777_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=299152 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_299925_299152_298377 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=776 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_383625_776_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=383161 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_383625_383161_382386 G hg ⟨f,hf⟩

end Signed39.Contraction
