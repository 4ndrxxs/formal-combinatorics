import Signed25Grid29Part0
import Signed25Grid29Part12
import Signed25Grid29Part24
import Signed25Grid29Part36
import Signed25Grid29Part48
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_29_25 : divisorGrid 29 25 264 qInputs_29_25 keep_29_25 := by
  intro d
  fin_cases d
  · exact grid29x25Case0
  · exact grid29x25Case1
  · exact grid29x25Case2
  · exact grid29x25Case3
  · exact grid29x25Case4
  · exact grid29x25Case5
  · exact grid29x25Case6
  · exact grid29x25Case7
  · exact grid29x25Case8
  · exact grid29x25Case9
  · exact grid29x25Case10
  · exact grid29x25Case11
  · exact grid29x25Case12
  · exact grid29x25Case13
  · exact grid29x25Case14
  · exact grid29x25Case15
  · exact grid29x25Case16
  · exact grid29x25Case17
  · exact grid29x25Case18
  · exact grid29x25Case19
  · exact grid29x25Case20
  · exact grid29x25Case21
  · exact grid29x25Case22
  · exact grid29x25Case23
  · exact grid29x25Case24
  · exact grid29x25Case25
  · exact grid29x25Case26
  · exact grid29x25Case27
  · exact grid29x25Case28
  · exact grid29x25Case29
  · exact grid29x25Case30
  · exact grid29x25Case31
  · exact grid29x25Case32
  · exact grid29x25Case33
  · exact grid29x25Case34
  · exact grid29x25Case35
  · exact grid29x25Case36
  · exact grid29x25Case37
  · exact grid29x25Case38
  · exact grid29x25Case39
  · exact grid29x25Case40
  · exact grid29x25Case41
  · exact grid29x25Case42
  · exact grid29x25Case43
  · exact grid29x25Case44
  · exact grid29x25Case45
  · exact grid29x25Case46
  · exact grid29x25Case47
  · exact grid29x25Case48
  · exact grid29x25Case49



private theorem frontier_mixed_1421_876_151 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1421) : ¬∃ f : G → ℤ, IsSDS 876 151 f :=
  abelian_short_linear G 29 49 26 1 5 7 876 151 25 16 18 31
    ⟨⟨1,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1421_1369_644 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1421) : ¬∃ f : G → ℤ, IsSDS 1369 644 f :=
  abelian_short_linear G 29 49 26 0 5 7 1369 644 25 33 18 31
    ⟨⟨8,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1711_729_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1711) : ¬∃ f : G → ℤ, IsSDS 729 4 f :=
  abelian_short_linear G 29 59 26 1 5 7 729 4 25 3 18 31
    ⟨⟨(-34),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1943_777_52 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1943) : ¬∃ f : G → ℤ, IsSDS 777 52 f :=
  abelian_short_linear G 29 67 26 1 5 7 777 52 25 11 18 31
    ⟨⟨(-34),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2059_1225_500 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2059) : ¬∃ f : G → ℤ, IsSDS 1225 500 f :=
  abelian_short_linear G 29 71 26 1 5 7 1225 500 25 35 18 31
    ⟨⟨(-420),(-33),25,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2059_1254_529 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2059) : ¬∃ f : G → ℤ, IsSDS 1254 529 f :=
  abelian_short_linear G 29 71 26 1 5 7 1254 529 25 36 18 31
    ⟨⟨(-1284367),(-74046),61746,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2407_753_28 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2407) : ¬∃ f : G → ℤ, IsSDS 753 28 f :=
  abelian_short_linear G 29 83 26 1 5 7 753 28 25 9 18 31
    ⟨⟨0,(-754),95,31⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,870,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2639_726_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2639) : ¬∃ f : G → ℤ, IsSDS 726 1 f :=
  abelian_short_linear G 29 91 26 1 5 7 726 1 25 2 18 31
    ⟨⟨(-765600),11600,15000,609⟩,[0,0,290000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2639_1161_436 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2639) : ¬∃ f : G → ℤ, IsSDS 1161 436 f :=
  abelian_short_linear G 29 91 26 1 5 7 1161 436 25 37 18 31
    ⟨⟨(-13572),0,413,(-9)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,3016,0,0,0,0,0,0,0,0,3886,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2639_1654_929 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2639) : ¬∃ f : G → ℤ, IsSDS 1654 929 f :=
  abelian_short_linear G 29 91 26 1 5 7 1654 929 25 54 18 31
    ⟨⟨(-2409675),0,31730,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,237808,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2987_1153_428 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2987) : ¬∃ f : G → ℤ, IsSDS 1153 428 f :=
  abelian_short_linear G 29 103 26 0 5 7 1153 428 25 39 18 31
    ⟨⟨(-57),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2987_1878_1153 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2987) : ¬∃ f : G → ℤ, IsSDS 1878 1153 f :=
  abelian_short_linear G 29 103 26 0 5 7 1878 1153 25 64 18 31
    ⟨⟨39,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3103_1137_412 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3103) : ¬∃ f : G → ℤ, IsSDS 1137 412 f :=
  abelian_short_linear G 29 107 26 0 5 7 1137 412 25 39 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3103_1978_1253 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3103) : ¬∃ f : G → ℤ, IsSDS 1978 1253 f :=
  abelian_short_linear G 29 107 26 0 5 7 1978 1253 25 68 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4321_900_175 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4321) : ¬∃ f : G → ℤ, IsSDS 900 175 f :=
  abelian_short_linear G 29 149 26 0 5 7 900 175 25 30 18 31
    ⟨⟨(-33),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4321_3481_2756 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4321) : ¬∃ f : G → ℤ, IsSDS 3481 2756 f :=
  abelian_short_linear G 29 149 26 0 5 7 3481 2756 25 119 18 31
    ⟨⟨(-123),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4379_774_49 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4379) : ¬∃ f : G → ℤ, IsSDS 774 49 f :=
  abelian_short_linear G 29 151 26 2 5 7 774 49 25 16 18 31
    ⟨⟨(-17893),(-1044),300,37⟩,[0,0,0,0,0,0,3625,0,0,0,0,0,0,0,0,0,6525,0,0,0,0,5800,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4379_4225_3500 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4379) : ¬∃ f : G → ℤ, IsSDS 4225 3500 f :=
  abelian_short_linear G 29 151 26 0 5 7 4225 3500 25 135 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5249_825_100 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5249) : ¬∃ f : G → ℤ, IsSDS 825 100 f :=
  abelian_short_linear G 29 181 26 1 5 7 825 100 25 25 18 31
    ⟨⟨0,(-1885),350,37⟩,[0,4350,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5249_4624_3899 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5249) : ¬∃ f : G → ℤ, IsSDS 4624 3899 f :=
  abelian_short_linear G 29 181 26 0 5 7 4624 3899 25 156 18 31
    ⟨⟨(-170),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10817_753_28 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10817) : ¬∃ f : G → ℤ, IsSDS 753 28 f :=
  abelian_short_linear G 29 373 26 3 5 7 753 28 25 19 18 31
    ⟨⟨(-45704),(-1798),675,31⟩,[0,0,0,0,0,11600,0,0,0,0,7250,0,0,0,0,0,0,0,0,7250,0,0,0,0,11600,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10817_10468_9743 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10817) : ¬∃ f : G → ℤ, IsSDS 10468 9743 f :=
  abelian_short_linear G 29 373 26 0 5 7 10468 9743 25 354 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12731_726_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12731) : ¬∃ f : G → ℤ, IsSDS 726 1 f :=
  abelian_short_linear G 29 439 26 7 5 7 726 1 25 4 18 31
    ⟨⟨(-1334),(-58),25,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13427_750_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13427) : ¬∃ f : G → ℤ, IsSDS 750 25 f :=
  abelian_short_linear G 29 463 26 2 5 7 750 25 25 20 18 31
    ⟨⟨0,(-7395),675,124⟩,[0,13050,0,0,0,0,0,0,0,0,0,2900,0,0,0,0,0,0,0,0,55100,0,0,0,0,59450,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13427_13017_12292 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13427) : ¬∃ f : G → ℤ, IsSDS 13017 12292 f :=
  abelian_short_linear G 29 463 26 0 5 7 13017 12292 25 443 18 31
    ⟨⟨(-463),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15863_753_28 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15863) : ¬∃ f : G → ℤ, IsSDS 753 28 f :=
  abelian_short_linear G 29 547 26 1 5 7 753 28 25 23 18 31
    ⟨⟨(-926),(-13),25,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15863_15282_14557 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15863) : ¬∃ f : G → ℤ, IsSDS 15282 14557 f :=
  abelian_short_linear G 29 547 26 0 5 7 15282 14557 25 524 18 31
    ⟨⟨499,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_16849_729_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=16849) : ¬∃ f : G → ℤ, IsSDS 729 4 f :=
  abelian_short_linear G 29 581 26 8 5 7 729 4 25 9 18 31
    ⟨⟨(-1483752000),(-71423500),41854171,0⟩,[0,0,0,0,0,0,0,0,0,198361000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_25259_729_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=25259) : ¬∃ f : G → ℤ, IsSDS 729 4 f :=
  abelian_short_linear G 29 871 26 7 5 7 729 4 25 11 18 31
    ⟨⟨(-49068),(-13079),1050,197⟩,[0,0,0,0,0,0,21750,0,0,0,0,42050,0,0,0,0,0,0,0,0,0,17400,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_29551_726_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=29551) : ¬∃ f : G → ℤ, IsSDS 726 1 f :=
  abelian_short_linear G 29 1019 26 9 5 7 726 1 25 6 18 31
    ⟨⟨(-1480),(-100),37,0⟩,[0,0,0,0,0,0,0,0,0,0,0,400,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_30653_732_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=30653) : ¬∃ f : G → ℤ, IsSDS 732 7 f :=
  abelian_short_linear G 29 1057 26 4 5 7 732 7 25 16 18 31
    ⟨⟨0,0,7440,(-7963)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_30653_30457_29732 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=30653) : ¬∃ f : G → ℤ, IsSDS 30457 29732 f :=
  abelian_short_linear G 29 1057 26 0 5 7 30457 29732 25 1041 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_37207_738_13 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=37207) : ¬∃ f : G → ℤ, IsSDS 738 13 f :=
  abelian_short_linear G 29 1283 26 0 5 7 738 13 25 24 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_37207_36553_35828 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=37207) : ¬∃ f : G → ℤ, IsSDS 36553 35828 f :=
  abelian_short_linear G 29 1283 26 0 5 7 36553 35828 25 1259 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_53099_726_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=53099) : ¬∃ f : G → ℤ, IsSDS 726 1 f :=
  abelian_short_linear G 29 1831 26 8 5 7 726 1 25 8 18 31
    ⟨⟨(-1134275000),(-19917869),19917869,0⟩,[0,0,0,168795500,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,543921000,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_60581_729_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=60581) : ¬∃ f : G → ℤ, IsSDS 729 4 f :=
  abelian_short_linear G 29 2089 26 4 5 7 729 4 25 17 18 31
    ⟨⟨0,(-29),14,(-43)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_60581_60324_59599 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=60581) : ¬∃ f : G → ℤ, IsSDS 60324 59599 f :=
  abelian_short_linear G 29 2089 26 0 5 7 60324 59599 25 2072 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_75719_729_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=75719) : ¬∃ f : G → ℤ, IsSDS 729 4 f :=
  abelian_short_linear G 29 2611 26 3 5 7 729 4 25 19 18 31
    ⟨⟨4,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_75719_75346_74621 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=75719) : ¬∃ f : G → ℤ, IsSDS 75346 74621 f :=
  abelian_short_linear G 29 2611 26 0 5 7 75346 74621 25 2592 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_92539_729_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=92539) : ¬∃ f : G → ℤ, IsSDS 729 4 f :=
  abelian_short_linear G 29 3191 26 2 5 7 729 4 25 21 18 31
    ⟨⟨1,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_92539_92050_91325 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=92539) : ¬∃ f : G → ℤ, IsSDS 92050 91325 f :=
  abelian_short_linear G 29 3191 26 0 5 7 92050 91325 25 3170 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_111041_729_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=111041) : ¬∃ f : G → ℤ, IsSDS 729 4 f :=
  abelian_short_linear G 29 3829 26 1 5 7 729 4 25 23 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_111041_110436_109711 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=111041) : ¬∃ f : G → ℤ, IsSDS 110436 109711 f :=
  abelian_short_linear G 29 3829 26 0 5 7 110436 109711 25 3806 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_164111_726_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=164111) : ¬∃ f : G → ℤ, IsSDS 726 1 f :=
  abelian_short_linear G 29 5659 26 5 5 7 726 1 25 14 18 31
    ⟨⟨0,0,11104,(-9689)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_164111_164025_163300 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=164111) : ¬∃ f : G → ℤ, IsSDS 164025 163300 f :=
  abelian_short_linear G 29 5659 26 0 5 7 164025 163300 25 5645 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_214571_726_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=214571) : ¬∃ f : G → ℤ, IsSDS 726 1 f :=
  abelian_short_linear G 29 7399 26 4 5 7 726 1 25 16 18 31
    ⟨⟨0,0,389,(-500)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_214571_214369_213644 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=214571) : ¬∃ f : G → ℤ, IsSDS 214369 213644 f :=
  abelian_short_linear G 29 7399 26 0 5 7 214369 213644 25 7383 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_271759_726_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=271759) : ¬∃ f : G → ℤ, IsSDS 726 1 f :=
  abelian_short_linear G 29 9371 26 3 5 7 726 1 25 18 18 31
    ⟨⟨8,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_271759_271441_270716 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=271759) : ¬∃ f : G → ℤ, IsSDS 271441 270716 f :=
  abelian_short_linear G 29 9371 26 0 5 7 271441 270716 25 9353 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_406319_726_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=406319) : ¬∃ f : G → ℤ, IsSDS 726 1 f :=
  abelian_short_linear G 29 14011 26 1 5 7 726 1 25 22 18 31
    ⟨⟨2,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_406319_405769_405044 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=406319) : ¬∃ f : G → ℤ, IsSDS 405769 405044 f :=
  abelian_short_linear G 29 14011 26 0 5 7 405769 405044 25 13989 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_483691_726_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=483691) : ¬∃ f : G → ℤ, IsSDS 726 1 f :=
  abelian_short_linear G 29 16679 26 0 5 7 726 1 25 24 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_483691_483025_482300 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=483691) : ¬∃ f : G → ℤ, IsSDS 483025 482300 f :=
  abelian_short_linear G 29 16679 26 0 5 7 483025 482300 25 16655 18 31
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_29_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=29*m)
    (hm : 29 < m) (hn : k-l=(29:ℤ)*25) : False := by
  let : Fact (Nat.Prime 29) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_29_25
  simp only [keep_29_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=876 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1421_876_151 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1369 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1421_1369_644 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=729 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1711_729_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=777 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1943_777_52 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2059_1225_500 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1254 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2059_1254_529 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=753 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2407_753_28 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=726 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2639_726_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1161 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2639_1161_436 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1654 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2639_1654_929 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1153 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2987_1153_428 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1878 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2987_1878_1153 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1137 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3103_1137_412 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1978 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3103_1978_1253 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=900 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4321_900_175 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3481 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4321_3481_2756 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=774 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4379_774_49 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4379_4225_3500 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=825 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5249_825_100 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4624 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5249_4624_3899 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=753 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10817_753_28 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=10468 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10817_10468_9743 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=726 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12731_726_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=750 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13427_750_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=13017 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13427_13017_12292 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=753 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15863_753_28 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=15282 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15863_15282_14557 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=729 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_16849_729_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=729 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_25259_729_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=726 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_29551_726_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=732 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_30653_732_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=30457 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_30653_30457_29732 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=738 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_37207_738_13 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=36553 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_37207_36553_35828 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=726 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_53099_726_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=729 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_60581_729_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=60324 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_60581_60324_59599 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=729 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_75719_729_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=75346 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_75719_75346_74621 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=729 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_92539_729_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=92050 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_92539_92050_91325 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=729 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_111041_729_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=110436 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_111041_110436_109711 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=726 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_164111_726_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=164025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_164111_164025_163300 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=726 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_214571_726_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=214369 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_214571_214369_213644 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=726 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_271759_726_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=271441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_271759_271441_270716 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=726 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_406319_726_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=405769 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_406319_405769_405044 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=726 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_483691_726_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=483025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_483691_483025_482300 G hg ⟨f,hf⟩

end Signed39.Contraction
