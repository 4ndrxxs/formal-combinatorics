import Signed25Grid37Part0
import Signed25Grid37Part12
import Signed25Grid37Part24
import Signed25Grid37Part36
import Signed25Grid37Part48
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_37_25 : divisorGrid 37 25 299 qInputs_37_25 keep_37_25 := by
  intro d
  fin_cases d
  · exact grid37x25Case0
  · exact grid37x25Case1
  · exact grid37x25Case2
  · exact grid37x25Case3
  · exact grid37x25Case4
  · exact grid37x25Case5
  · exact grid37x25Case6
  · exact grid37x25Case7
  · exact grid37x25Case8
  · exact grid37x25Case9
  · exact grid37x25Case10
  · exact grid37x25Case11
  · exact grid37x25Case12
  · exact grid37x25Case13
  · exact grid37x25Case14
  · exact grid37x25Case15
  · exact grid37x25Case16
  · exact grid37x25Case17
  · exact grid37x25Case18
  · exact grid37x25Case19
  · exact grid37x25Case20
  · exact grid37x25Case21
  · exact grid37x25Case22
  · exact grid37x25Case23
  · exact grid37x25Case24
  · exact grid37x25Case25
  · exact grid37x25Case26
  · exact grid37x25Case27
  · exact grid37x25Case28
  · exact grid37x25Case29
  · exact grid37x25Case30
  · exact grid37x25Case31
  · exact grid37x25Case32
  · exact grid37x25Case33
  · exact grid37x25Case34
  · exact grid37x25Case35
  · exact grid37x25Case36
  · exact grid37x25Case37
  · exact grid37x25Case38
  · exact grid37x25Case39
  · exact grid37x25Case40
  · exact grid37x25Case41
  · exact grid37x25Case42
  · exact grid37x25Case43
  · exact grid37x25Case44
  · exact grid37x25Case45
  · exact grid37x25Case46
  · exact grid37x25Case47
  · exact grid37x25Case48
  · exact grid37x25Case49



private theorem frontier_mixed_1517_928_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1517) : ¬∃ f : G → ℤ, IsSDS 928 3 f :=
  abelian_short_linear G 37 41 30 0 5 18 928 3 25 2 20 27
    ⟨⟨(-38),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1739_1126_201 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1739) : ¬∃ f : G → ℤ, IsSDS 1126 201 f :=
  abelian_short_linear G 37 47 30 0 5 18 1126 201 25 16 20 27
    ⟨⟨(-4),(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1739_1681_756 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1739) : ¬∃ f : G → ℤ, IsSDS 1681 756 f :=
  abelian_short_linear G 37 47 30 0 5 18 1681 756 25 31 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1813_1000_75 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1813) : ¬∃ f : G → ℤ, IsSDS 1000 75 f :=
  abelian_short_linear G 37 49 30 0 5 18 1000 75 25 10 20 27
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2331_934_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2331) : ¬∃ f : G → ℤ, IsSDS 934 9 f :=
  abelian_short_linear G 37 63 30 1 5 18 934 9 25 4 20 27
    ⟨⟨(-47),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2331_1489_564 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2331) : ¬∃ f : G → ℤ, IsSDS 1489 564 f :=
  abelian_short_linear G 37 63 30 0 5 18 1489 564 25 31 20 27
    ⟨⟨1,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2331_1526_601 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2331) : ¬∃ f : G → ℤ, IsSDS 1526 601 f :=
  abelian_short_linear G 37 63 30 0 5 18 1526 601 25 32 20 27
    ⟨⟨17,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2479_1066_141 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2479) : ¬∃ f : G → ℤ, IsSDS 1066 141 f :=
  abelian_short_linear G 37 67 30 1 5 18 1066 141 25 16 20 27
    ⟨⟨(-40),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2479_2361_1436 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2479) : ¬∃ f : G → ℤ, IsSDS 2361 1436 f :=
  abelian_short_linear G 37 67 30 0 5 18 2361 1436 25 51 20 27
    ⟨⟨26,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2627_958_33 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2627) : ¬∃ f : G → ℤ, IsSDS 958 33 f :=
  abelian_short_linear G 37 71 30 1 5 18 958 33 25 8 20 27
    ⟨⟨(-48),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2701_1024_99 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2701) : ¬∃ f : G → ℤ, IsSDS 1024 99 f :=
  abelian_short_linear G 37 73 30 1 5 18 1024 99 25 14 20 27
    ⟨⟨9,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2701_2689_1764 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2701) : ¬∃ f : G → ℤ, IsSDS 2689 1764 f :=
  abelian_short_linear G 37 73 30 0 5 18 2689 1764 25 59 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2849_929_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2849) : ¬∃ f : G → ℤ, IsSDS 929 4 f :=
  abelian_short_linear G 37 77 30 1 5 18 929 4 25 3 20 27
    ⟨⟨(-21024288),(-158175),493250,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1825025,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2849_1225_300 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2849) : ¬∃ f : G → ℤ, IsSDS 1225 300 f :=
  abelian_short_linear G 37 77 30 1 5 18 1225 300 25 25 20 27
    ⟨⟨15,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2849_2224_1299 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2849) : ¬∃ f : G → ℤ, IsSDS 2224 1299 f :=
  abelian_short_linear G 37 77 30 0 5 18 2224 1299 25 52 20 27
    ⟨⟨(-70),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2997_932_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2997) : ¬∃ f : G → ℤ, IsSDS 932 7 f :=
  abelian_short_linear G 37 81 30 1 5 18 932 7 25 4 20 27
    ⟨⟨(-9768),(-481),175,12⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7400,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3071_1025_100 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3071) : ¬∃ f : G → ℤ, IsSDS 1025 100 f :=
  abelian_short_linear G 37 83 30 1 5 18 1025 100 25 15 20 27
    ⟨⟨0,(-53),25,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3071_2986_2061 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3071) : ¬∃ f : G → ℤ, IsSDS 2986 2061 f :=
  abelian_short_linear G 37 83 30 0 5 18 2986 2061 25 68 20 27
    ⟨⟨5169411,25312,(-87584),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3663_998_73 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3663) : ¬∃ f : G → ℤ, IsSDS 998 73 f :=
  abelian_short_linear G 37 99 30 1 5 18 998 73 25 14 20 27
    ⟨⟨0,(-36667),2610,1013⟩,[0,0,0,0,5180,0,0,0,0,0,0,0,0,0,132090,0,0,0,0,208310,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3663_1553_628 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3663) : ¬∃ f : G → ℤ, IsSDS 1553 628 f :=
  abelian_short_linear G 37 99 30 0 5 18 1553 628 25 41 20 27
    ⟨⟨(-46),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3663_2182_1257 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3663) : ¬∃ f : G → ℤ, IsSDS 2182 1257 f :=
  abelian_short_linear G 37 99 30 0 5 18 2182 1257 25 58 20 27
    ⟨⟨53,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3663_3625_2700 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3663) : ¬∃ f : G → ℤ, IsSDS 3625 2700 f :=
  abelian_short_linear G 37 99 30 0 5 18 3625 2700 25 85 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3737_1057_132 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3737) : ¬∃ f : G → ℤ, IsSDS 1057 132 f :=
  abelian_short_linear G 37 101 30 1 5 18 1057 132 25 19 20 27
    ⟨⟨0,(-3034),340,71⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15355,0,0,0,0,0,0,0,0,0,2775,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3737_3388_2463 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3737) : ¬∃ f : G → ℤ, IsSDS 3388 2463 f :=
  abelian_short_linear G 37 101 30 0 5 18 3388 2463 25 82 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4477_1200_275 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4477) : ¬∃ f : G → ℤ, IsSDS 1200 275 f :=
  abelian_short_linear G 37 121 30 1 5 18 1200 275 25 30 20 27
    ⟨⟨0,(-2590),1125,17⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4477_3457_2532 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4477) : ¬∃ f : G → ℤ, IsSDS 3457 2532 f :=
  abelian_short_linear G 37 121 30 0 5 18 3457 2532 25 91 20 27
    ⟨⟨(-98000),899,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4551_926_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4551) : ¬∃ f : G → ℤ, IsSDS 926 1 f :=
  abelian_short_linear G 37 123 30 2 5 18 926 1 25 2 20 27
    ⟨⟨(-1406),(-74),25,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4699_1009_84 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4699) : ¬∃ f : G → ℤ, IsSDS 1009 84 f :=
  abelian_short_linear G 37 127 30 1 5 18 1009 84 25 17 20 27
    ⟨⟨(-5550),37,90,0⟩,[0,0,0,0,0,0,0,1110,0,0,0,0,1110,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4699_4450_3525 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4699) : ¬∃ f : G → ℤ, IsSDS 4450 3525 f :=
  abelian_short_linear G 37 127 30 0 5 18 4450 3525 25 110 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5217_992_67 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5217) : ¬∃ f : G → ℤ, IsSDS 992 67 f :=
  abelian_short_linear G 37 141 30 2 5 18 992 67 25 16 20 27
    ⟨⟨0,(-2701),195,86⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11840,0,0,0,0,2220,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5217_1177_252 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5217) : ¬∃ f : G → ℤ, IsSDS 1177 252 f :=
  abelian_short_linear G 37 141 30 0 5 18 1177 252 25 31 20 27
    ⟨⟨(-920094),(-19600),28825,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5217_4100_3175 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5217) : ¬∃ f : G → ℤ, IsSDS 4100 3175 f :=
  abelian_short_linear G 37 141 30 0 5 18 4100 3175 25 110 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5217_5025_4100 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5217) : ¬∃ f : G → ℤ, IsSDS 5025 4100 f :=
  abelian_short_linear G 37 141 30 0 5 18 5025 4100 25 125 20 27
    ⟨⟨100,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5439_950_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5439) : ¬∃ f : G → ℤ, IsSDS 950 25 f :=
  abelian_short_linear G 37 147 30 2 5 18 950 25 25 10 20 27
    ⟨⟨0,(-4255),375,116⟩,[0,0,0,0,0,0,0,0,0,0,12950,0,0,0,0,11100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5513_937_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5513) : ¬∃ f : G → ℤ, IsSDS 937 12 f :=
  abelian_short_linear G 37 149 30 2 5 18 937 12 25 7 20 27
    ⟨⟨(-1565100),1887,18750,1887⟩,[0,0,92500,0,0,0,0,555000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,277500,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6993_928_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6993) : ¬∃ f : G → ℤ, IsSDS 928 3 f :=
  abelian_short_linear G 37 189 30 2 5 18 928 3 25 4 20 27
    ⟨⟨(-58904),(-1998),875,31⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,5550,0,0,0,0,14800,0,0,0,0,0,0,0,0,0,0,0,5550,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7289_1000_75 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7289) : ¬∃ f : G → ℤ, IsSDS 1000 75 f :=
  abelian_short_linear G 37 197 30 2 5 18 1000 75 25 20 20 27
    ⟨⟨0,(-6290),375,163⟩,[0,0,0,0,0,0,0,0,0,0,20350,0,0,0,0,5550,0,0,0,0,38850,0,0,0,0,9250,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7289_6809_5884 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7289) : ¬∃ f : G → ℤ, IsSDS 6809 5884 f :=
  abelian_short_linear G 37 197 30 0 5 18 6809 5884 25 177 20 27
    ⟨⟨(-197),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7437_972_47 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7437) : ¬∃ f : G → ℤ, IsSDS 972 47 f :=
  abelian_short_linear G 37 201 30 2 5 18 972 47 25 16 20 27
    ⟨⟨(-9287),(-444),120,11⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2775,0,0,0,0,0,0,0,0,0,4995,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7437_7225_6300 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7437) : ¬∃ f : G → ℤ, IsSDS 7225 6300 f :=
  abelian_short_linear G 37 201 30 0 5 18 7225 6300 25 185 20 27
    ⟨⟨160,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7881_936_11 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7881) : ¬∃ f : G → ℤ, IsSDS 936 11 f :=
  abelian_short_linear G 37 213 30 3 5 18 936 11 25 8 20 27
    ⟨⟨(-1052678000),(-35684000),10850000,1935857⟩,[0,0,0,356840000,0,0,0,0,89210000,0,0,0,0,0,0,0,0,0,89210000,0,0,0,0,356840000,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8103_958_33 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8103) : ¬∃ f : G → ℤ, IsSDS 958 33 f :=
  abelian_short_linear G 37 219 30 3 5 18 958 33 25 14 20 27
    ⟨⟨0,(-61901),10450,1029⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,58830,0,0,0,0,0,0,0,0,0,0,0,0,0,0,250490,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8103_8025_7100 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8103) : ¬∃ f : G → ℤ, IsSDS 8025 7100 f :=
  abelian_short_linear G 37 219 30 0 5 18 8025 7100 25 205 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8547_1025_100 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8547) : ¬∃ f : G → ℤ, IsSDS 1025 100 f :=
  abelian_short_linear G 37 231 30 1 5 18 1025 100 25 25 20 27
    ⟨⟨0,(-3708375),410000,73718⟩,[0,0,0,0,0,0,0,0,0,0,12361250,0,0,0,0,0,0,0,0,0,5618750,0,0,0,0,0,0,0,0,0,10113750,0,0,0,0,8990000,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8547_7722_6797 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8547) : ¬∃ f : G → ℤ, IsSDS 7722 6797 f :=
  abelian_short_linear G 37 231 30 0 5 18 7722 6797 25 206 20 27
    ⟨⟨(-218),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11211_969_44 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11211) : ¬∃ f : G → ℤ, IsSDS 969 44 f :=
  abelian_short_linear G 37 303 30 3 5 18 969 44 25 19 20 27
    ⟨⟨(-57646),(-10952),875,319⟩,[0,0,0,0,1850,0,0,0,0,0,0,0,0,0,59200,0,0,0,0,49950,0,0,0,0,37000,0,0,0,0,20350,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11211_10774_9849 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11211) : ¬∃ f : G → ℤ, IsSDS 10774 9849 f :=
  abelian_short_linear G 37 303 30 0 5 18 10774 9849 25 284 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14097_953_28 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14097) : ¬∃ f : G → ℤ, IsSDS 953 28 f :=
  abelian_short_linear G 37 381 30 4 5 18 953 28 25 17 20 27
    ⟨⟨(-6808),0,63,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,814,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14097_13792_12867 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14097) : ¬∃ f : G → ℤ, IsSDS 13792 12867 f :=
  abelian_short_linear G 37 381 30 0 5 18 13792 12867 25 364 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_16539_929_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=16539) : ¬∃ f : G → ℤ, IsSDS 929 4 f :=
  abelian_short_linear G 37 447 30 6 5 18 929 4 25 7 20 27
    ⟨⟨(-34188),(-1702),375,23⟩,[0,0,0,0,0,0,0,1850,0,0,0,0,5550,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20979_926_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20979) : ¬∃ f : G → ℤ, IsSDS 926 1 f :=
  abelian_short_linear G 37 567 30 8 5 18 926 1 25 4 20 27
    ⟨⟨(-110083806),(-6115767),1458450,418100⟩,[0,0,0,0,0,0,0,0,0,53962650,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_21867_950_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=21867) : ¬∃ f : G → ℤ, IsSDS 950 25 f :=
  abelian_short_linear G 37 591 30 2 5 18 950 25 25 20 20 27
    ⟨⟨0,(-1881746),64650,58275⟩,[0,0,0,0,0,0,0,0,0,0,318940,0,0,0,0,956820,0,0,0,0,1913640,0,0,0,0,3189400,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_21867_21337_20412 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=21867) : ¬∃ f : G → ℤ, IsSDS 21337 20412 f :=
  abelian_short_linear G 37 591 30 0 5 18 21337 20412 25 571 20 27
    ⟨⟨(-591),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_24309_936_11 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=24309) : ¬∃ f : G → ℤ, IsSDS 936 11 f :=
  abelian_short_linear G 37 657 30 5 5 18 936 11 25 14 20 27
    ⟨⟨(-62160),(-20720),1000,851⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_24309_24209_23284 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=24309) : ¬∃ f : G → ℤ, IsSDS 24209 23284 f :=
  abelian_short_linear G 37 657 30 0 5 18 24209 23284 25 643 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_27491_929_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=27491) : ¬∃ f : G → ℤ, IsSDS 929 4 f :=
  abelian_short_linear G 37 743 30 8 5 18 929 4 25 9 20 27
    ⟨⟨(-64491),(-5032),600,59⟩,[0,0,0,0,21275,0,0,0,0,0,0,0,0,0,24975,0,0,0,0,7400,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28897_928_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28897) : ¬∃ f : G → ℤ, IsSDS 928 3 f :=
  abelian_short_linear G 37 781 30 8 5 18 928 3 25 8 20 27
    ⟨⟨(-25974),(-3034),525,(-11)⟩,[0,0,0,0,0,0,0,0,3700,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_29711_934_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=29711) : ¬∃ f : G → ℤ, IsSDS 934 9 f :=
  abelian_short_linear G 37 803 30 5 5 18 934 9 25 14 20 27
    ⟨⟨0,(-1755297500),71945720,55757933⟩,[0,0,0,0,285572000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_29711_29609_28684 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=29711) : ¬∃ f : G → ℤ, IsSDS 29609 28684 f :=
  abelian_short_linear G 37 803 30 0 5 18 29609 28684 25 789 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_32893_937_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=32893) : ¬∃ f : G → ℤ, IsSDS 937 12 f :=
  abelian_short_linear G 37 889 30 4 5 18 937 12 25 17 20 27
    ⟨⟨(-61309),(-6216),500,129⟩,[0,0,34225,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_32893_32572_31647 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=32893) : ¬∃ f : G → ℤ, IsSDS 32572 31647 f :=
  abelian_short_linear G 37 889 30 0 5 18 32572 31647 25 872 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_41107_937_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=41107) : ¬∃ f : G → ℤ, IsSDS 937 12 f :=
  abelian_short_linear G 37 1111 30 3 5 18 937 12 25 19 20 27
    ⟨⟨(-18611),(-3552),200,59⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_41107_40638_39713 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=41107) : ¬∃ f : G → ℤ, IsSDS 40638 39713 f :=
  abelian_short_linear G 37 1111 30 0 5 18 40638 39713 25 1092 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_48359_926_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=48359) : ¬∃ f : G → ℤ, IsSDS 926 1 f :=
  abelian_short_linear G 37 1307 30 9 5 18 926 1 25 6 20 27
    ⟨⟨(-1554),(-222),25,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_73519_934_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=73519) : ¬∃ f : G → ℤ, IsSDS 934 9 f :=
  abelian_short_linear G 37 1987 30 1 5 18 934 9 25 22 20 27
    ⟨⟨2,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_73519_72825_71900 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=73519) : ¬∃ f : G → ℤ, IsSDS 72825 71900 f :=
  abelian_short_linear G 37 1987 30 0 5 18 72825 71900 25 1965 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_86691_926_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=86691) : ¬∃ f : G → ℤ, IsSDS 926 1 f :=
  abelian_short_linear G 37 2343 30 8 5 18 926 1 25 8 20 27
    ⟨⟨(-4366),(-333),60,0⟩,[0,0,0,2590,0,0,0,0,1110,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_89133_928_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=89133) : ¬∃ f : G → ℤ, IsSDS 928 3 f :=
  abelian_short_linear G 37 2409 30 5 5 18 928 3 25 14 20 27
    ⟨⟨0,0,361,(-377)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_89133_89025_88100 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=89133) : ¬∃ f : G → ℤ, IsSDS 89025 88100 f :=
  abelian_short_linear G 37 2409 30 0 5 18 89025 88100 25 2395 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_98679_929_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=98679) : ¬∃ f : G → ℤ, IsSDS 929 4 f :=
  abelian_short_linear G 37 2667 30 4 5 18 929 4 25 17 20 27
    ⟨⟨0,0,32,(-97)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_98679_98350_97425 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=98679) : ¬∃ f : G → ℤ, IsSDS 98350 97425 f :=
  abelian_short_linear G 37 2667 30 0 5 18 98350 97425 25 2650 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_116513_928_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=116513) : ¬∃ f : G → ℤ, IsSDS 928 3 f :=
  abelian_short_linear G 37 3149 30 4 5 18 928 3 25 16 20 27
    ⟨⟨0,(-1776),275,(-559)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_116513_116257_115332 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=116513) : ¬∃ f : G → ℤ, IsSDS 116257 115332 f :=
  abelian_short_linear G 37 3149 30 0 5 18 116257 115332 25 3133 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_123321_929_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=123321) : ¬∃ f : G → ℤ, IsSDS 929 4 f :=
  abelian_short_linear G 37 3333 30 3 5 18 929 4 25 19 20 27
    ⟨⟨4,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_123321_122844_121919 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=123321) : ¬∃ f : G → ℤ, IsSDS 122844 121919 f :=
  abelian_short_linear G 37 3333 30 0 5 18 122844 121919 25 3314 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_196211_926_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=196211) : ¬∃ f : G → ℤ, IsSDS 926 1 f :=
  abelian_short_linear G 37 5303 30 6 5 18 926 1 25 12 20 27
    ⟨⟨(-666),(-444),25,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_220557_928_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=220557) : ¬∃ f : G → ℤ, IsSDS 928 3 f :=
  abelian_short_linear G 37 5961 30 1 5 18 928 3 25 22 20 27
    ⟨⟨2,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_220557_219857_218932 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=220557) : ¬∃ f : G → ℤ, IsSDS 219857 218932 f :=
  abelian_short_linear G 37 5961 30 0 5 18 219857 218932 25 5939 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_267399_926_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=267399) : ¬∃ f : G → ℤ, IsSDS 926 1 f :=
  abelian_short_linear G 37 7227 30 5 5 18 926 1 25 14 20 27
    ⟨⟨0,0,361,(-397)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_267399_267289_266364 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=267399) : ¬∃ f : G → ℤ, IsSDS 267289 266364 f :=
  abelian_short_linear G 37 7227 30 0 5 18 267289 266364 25 7213 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_349539_926_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=349539) : ¬∃ f : G → ℤ, IsSDS 926 1 f :=
  abelian_short_linear G 37 9447 30 4 5 18 926 1 25 16 20 27
    ⟨⟨0,(-888),135,(-557)⟩,[0,0,0,0,0,0,0,0,0,0,0,36260,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_349539_349281_348356 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=349539) : ¬∃ f : G → ℤ, IsSDS 349281 348356 f :=
  abelian_short_linear G 37 9447 30 0 5 18 349281 348356 25 9431 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_661671_926_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=661671) : ¬∃ f : G → ℤ, IsSDS 926 1 f :=
  abelian_short_linear G 37 17883 30 1 5 18 926 1 25 22 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_661671_660969_660044 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=661671) : ¬∃ f : G → ℤ, IsSDS 660969 660044 f :=
  abelian_short_linear G 37 17883 30 0 5 18 660969 660044 25 17861 20 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_37_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=37*m)
    (hm : 37 < m) (hn : k-l=(37:ℤ)*25) : False := by
  let : Fact (Nat.Prime 37) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_37_25
  simp only [keep_37_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=928 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1517_928_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1126 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1739_1126_201 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1681 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1739_1681_756 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1000 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1813_1000_75 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=934 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2331_934_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1489 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2331_1489_564 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1526 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2331_1526_601 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1066 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2479_1066_141 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2361 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2479_2361_1436 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=958 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2627_958_33 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1024 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2701_1024_99 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2689 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2701_2689_1764 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=929 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2849_929_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2849_1225_300 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2224 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2849_2224_1299 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=932 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2997_932_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3071_1025_100 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2986 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3071_2986_2061 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=998 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3663_998_73 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1553 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3663_1553_628 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2182 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3663_2182_1257 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3663_3625_2700 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1057 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3737_1057_132 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3388 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3737_3388_2463 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1200 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4477_1200_275 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3457 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4477_3457_2532 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=926 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4551_926_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1009 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4699_1009_84 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4450 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4699_4450_3525 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=992 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5217_992_67 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5217_1177_252 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4100 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5217_4100_3175 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5217_5025_4100 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=950 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5439_950_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=937 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5513_937_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=928 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6993_928_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1000 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7289_1000_75 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6809 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7289_6809_5884 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=972 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7437_972_47 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7437_7225_6300 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=936 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7881_936_11 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=958 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8103_958_33 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=8025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8103_8025_7100 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8547_1025_100 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7722 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8547_7722_6797 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=969 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11211_969_44 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=10774 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11211_10774_9849 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=953 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14097_953_28 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=13792 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14097_13792_12867 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=929 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_16539_929_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=926 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20979_926_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=950 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_21867_950_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=21337 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_21867_21337_20412 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=936 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_24309_936_11 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=24209 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_24309_24209_23284 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=929 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_27491_929_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=928 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28897_928_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=934 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_29711_934_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=29609 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_29711_29609_28684 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=937 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_32893_937_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=32572 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_32893_32572_31647 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=937 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_41107_937_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=40638 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_41107_40638_39713 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=926 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_48359_926_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=934 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_73519_934_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=72825 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_73519_72825_71900 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=926 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_86691_926_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=928 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_89133_928_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=89025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_89133_89025_88100 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=929 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_98679_929_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=98350 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_98679_98350_97425 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=928 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_116513_928_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=116257 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_116513_116257_115332 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=929 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_123321_929_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=122844 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_123321_122844_121919 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=926 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_196211_926_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=928 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_220557_928_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=219857 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_220557_219857_218932 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=926 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_267399_926_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=267289 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_267399_267289_266364 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=926 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_349539_926_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=349281 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_349539_349281_348356 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=926 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_661671_926_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=660969 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_661671_660969_660044 G hg ⟨f,hf⟩

end Signed39.Contraction
