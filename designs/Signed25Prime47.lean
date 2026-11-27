import Signed25Grid47Part0
import Signed25Grid47Part12
import Signed25Grid47Part24
import Signed25Grid47Part36
import Signed25Grid47Part48
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_47_25 : divisorGrid 47 25 336 qInputs_47_25 keep_47_25 := by
  intro d
  fin_cases d
  · exact grid47x25Case0
  · exact grid47x25Case1
  · exact grid47x25Case2
  · exact grid47x25Case3
  · exact grid47x25Case4
  · exact grid47x25Case5
  · exact grid47x25Case6
  · exact grid47x25Case7
  · exact grid47x25Case8
  · exact grid47x25Case9
  · exact grid47x25Case10
  · exact grid47x25Case11
  · exact grid47x25Case12
  · exact grid47x25Case13
  · exact grid47x25Case14
  · exact grid47x25Case15
  · exact grid47x25Case16
  · exact grid47x25Case17
  · exact grid47x25Case18
  · exact grid47x25Case19
  · exact grid47x25Case20
  · exact grid47x25Case21
  · exact grid47x25Case22
  · exact grid47x25Case23
  · exact grid47x25Case24
  · exact grid47x25Case25
  · exact grid47x25Case26
  · exact grid47x25Case27
  · exact grid47x25Case28
  · exact grid47x25Case29
  · exact grid47x25Case30
  · exact grid47x25Case31
  · exact grid47x25Case32
  · exact grid47x25Case33
  · exact grid47x25Case34
  · exact grid47x25Case35
  · exact grid47x25Case36
  · exact grid47x25Case37
  · exact grid47x25Case38
  · exact grid47x25Case39
  · exact grid47x25Case40
  · exact grid47x25Case41
  · exact grid47x25Case42
  · exact grid47x25Case43
  · exact grid47x25Case44
  · exact grid47x25Case45
  · exact grid47x25Case46
  · exact grid47x25Case47
  · exact grid47x25Case48
  · exact grid47x25Case49



private theorem frontier_mixed_2491_1774_599 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2491) : ¬∃ f : G → ℤ, IsSDS 1774 599 f :=
  abelian_short_linear G 47 53 33 0 5 23 1774 599 25 26 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2491_1821_646 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2491) : ¬∃ f : G → ℤ, IsSDS 1821 646 f :=
  abelian_short_linear G 47 53 33 0 5 23 1821 646 25 27 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2867_1237_62 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2867) : ¬∃ f : G → ℤ, IsSDS 1237 62 f :=
  abelian_short_linear G 47 61 33 0 5 23 1237 62 25 9 16 17
    ⟨⟨(-11),(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3149_1209_34 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3149) : ¬∃ f : G → ℤ, IsSDS 1209 34 f :=
  abelian_short_linear G 47 67 33 0 5 23 1209 34 25 7 16 17
    ⟨⟨2,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5029_1249_74 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5029) : ¬∃ f : G → ℤ, IsSDS 1249 74 f :=
  abelian_short_linear G 47 107 33 1 5 23 1249 74 25 13 16 17
    ⟨⟨(-1319626497),0,18102805,0⟩,[0,0,0,0,0,0,0,0,65871045,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7379_1194_19 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7379) : ¬∃ f : G → ℤ, IsSDS 1194 19 f :=
  abelian_short_linear G 47 157 33 1 5 23 1194 19 25 8 16 17
    ⟨⟨(-3290),0,31,1⟩,[0,0,0,0,0,0,0,0,188,0,0,0,0,0,0,0,0,0,0,0,0,0,0,188,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7661_1176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7661) : ¬∃ f : G → ℤ, IsSDS 1176 1 f :=
  abelian_short_linear G 47 163 33 2 5 23 1176 1 25 2 16 17
    ⟨⟨(-6800),0,189,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9353_1177_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9353) : ¬∃ f : G → ℤ, IsSDS 1177 2 f :=
  abelian_short_linear G 47 199 33 2 5 23 1177 2 25 3 16 17
    ⟨⟨(-8460000),0,70000,28623⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,235000,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9917_1225_50 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9917) : ¬∃ f : G → ℤ, IsSDS 1225 50 f :=
  abelian_short_linear G 47 211 33 2 5 23 1225 50 25 15 16 17
    ⟨⟨0,(-5405),250,171⟩,[0,0,0,0,0,0,0,0,0,0,16450,0,0,0,0,25850,0,0,0,0,4700,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9917_9732_8557 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9917) : ¬∃ f : G → ℤ, IsSDS 9732 8557 f :=
  abelian_short_linear G 47 211 33 0 5 23 9732 8557 25 196 16 17
    ⟨⟨(-211),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_27589_1225_50 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=27589) : ¬∃ f : G → ℤ, IsSDS 1225 50 f :=
  abelian_short_linear G 47 587 33 0 5 23 1225 50 25 25 16 17
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_27589_26464_25289 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=27589) : ¬∃ f : G → ℤ, IsSDS 26464 25289 f :=
  abelian_short_linear G 47 587 33 0 5 23 26464 25289 25 562 16 17
    ⟨⟨(-587),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28153_1228_53 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28153) : ¬∃ f : G → ℤ, IsSDS 1228 53 f :=
  abelian_short_linear G 47 599 33 0 5 23 1228 53 25 26 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28153_26937_25762 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28153) : ¬∃ f : G → ℤ, IsSDS 26937 25762 f :=
  abelian_short_linear G 47 599 33 0 5 23 26937 25762 25 573 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_34169_1176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=34169) : ¬∃ f : G → ℤ, IsSDS 1176 1 f :=
  abelian_short_linear G 47 727 33 8 5 23 1176 1 25 4 16 17
    ⟨⟨(-1692),(-47),15,10⟩,[0,0,0,0,940,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_35297_1200_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=35297) : ¬∃ f : G → ℤ, IsSDS 1200 25 f :=
  abelian_short_linear G 47 751 33 2 5 23 1200 25 25 20 16 17
    ⟨⟨0,(-4000),151,151⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_35297_34617_33442 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=35297) : ¬∃ f : G → ℤ, IsSDS 34617 33442 f :=
  abelian_short_linear G 47 751 33 0 5 23 34617 33442 25 731 16 17
    ⟨⟨(-751),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_44227_1197_22 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=44227) : ¬∃ f : G → ℤ, IsSDS 1197 22 f :=
  abelian_short_linear G 47 941 33 2 5 23 1197 22 25 21 16 17
    ⟨⟨0,(-16933750),0,729771⟩,[0,16520000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_44227_43450_42275 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=44227) : ¬∃ f : G → ℤ, IsSDS 43450 42275 f :=
  abelian_short_linear G 47 941 33 0 5 23 43450 42275 25 920 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_74777_1192_17 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=74777) : ¬∃ f : G → ℤ, IsSDS 1192 17 f :=
  abelian_short_linear G 47 1591 33 0 5 23 1192 17 25 24 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_74777_73713_72538 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=74777) : ¬∃ f : G → ℤ, IsSDS 73713 72538 f :=
  abelian_short_linear G 47 1591 33 0 5 23 73713 72538 25 1567 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_78349_1176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=78349) : ¬∃ f : G → ℤ, IsSDS 1176 1 f :=
  abelian_short_linear G 47 1667 33 9 5 23 1176 1 25 6 16 17
    ⟨⟨(-52680044),(-5501397),532050,188000⟩,[0,0,0,0,0,0,41677250,0,0,0,0,25006350,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_88877_1177_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=88877) : ¬∃ f : G → ℤ, IsSDS 1177 2 f :=
  abelian_short_linear G 47 1891 33 8 5 23 1177 2 25 9 16 17
    ⟨⟨(-34968),(-6016),375,77⟩,[0,0,0,0,18800,0,0,0,0,0,0,0,0,0,14100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_140201_1176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=140201) : ¬∃ f : G → ℤ, IsSDS 1176 1 f :=
  abelian_short_linear G 47 2983 33 8 5 23 1176 1 25 8 16 17
    ⟨⟨(-2256),(-376),25,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_186073_1177_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=186073) : ¬∃ f : G → ℤ, IsSDS 1177 2 f :=
  abelian_short_linear G 47 3959 33 6 5 23 1177 2 25 13 16 17
    ⟨⟨0,0,2043,(-2500)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_186073_186028_184853 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=186073) : ¬∃ f : G → ℤ, IsSDS 186028 184853 f :=
  abelian_short_linear G 47 3959 33 0 5 23 186028 184853 25 3946 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_318613_1177_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=318613) : ¬∃ f : G → ℤ, IsSDS 1177 2 f :=
  abelian_short_linear G 47 6779 33 4 5 23 1177 2 25 17 16 17
    ⟨⟨0,0,12,(-31)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_318613_318192_317017 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=318613) : ¬∃ f : G → ℤ, IsSDS 318192 317017 f :=
  abelian_short_linear G 47 6779 33 0 5 23 318192 317017 25 6762 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_431789_1176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=431789) : ¬∃ f : G → ℤ, IsSDS 1176 1 f :=
  abelian_short_linear G 47 9187 33 5 5 23 1176 1 25 14 16 17
    ⟨⟨0,0,2389,(-2500)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_431789_431649_430474 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=431789) : ¬∃ f : G → ℤ, IsSDS 431649 430474 f :=
  abelian_short_linear G 47 9187 33 0 5 23 431649 430474 25 9173 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_486497_1177_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=486497) : ¬∃ f : G → ℤ, IsSDS 1177 2 f :=
  abelian_short_linear G 47 10351 33 2 5 23 1177 2 25 21 16 17
    ⟨⟨1,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_486497_485700_484525 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=486497) : ¬∃ f : G → ℤ, IsSDS 485700 484525 f :=
  abelian_short_linear G 47 10351 33 0 5 23 485700 484525 25 10330 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_564329_1176_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=564329) : ¬∃ f : G → ℤ, IsSDS 1176 1 f :=
  abelian_short_linear G 47 12007 33 4 5 23 1176 1 25 16 16 17
    ⟨⟨0,0,121,(-405)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_564329_564001_562826 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=564329) : ¬∃ f : G → ℤ, IsSDS 564001 562826 f :=
  abelian_short_linear G 47 12007 33 0 5 23 564001 562826 25 11991 16 17
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_47_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=47*m)
    (hm : 47 < m) (hn : k-l=(47:ℤ)*25) : False := by
  let : Fact (Nat.Prime 47) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_47_25
  simp only [keep_47_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1774 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2491_1774_599 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1821 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2491_1821_646 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1237 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2867_1237_62 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1209 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3149_1209_34 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1249 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5029_1249_74 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1194 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7379_1194_19 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7661_1176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9353_1177_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9917_1225_50 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=9732 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9917_9732_8557 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_27589_1225_50 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=26464 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_27589_26464_25289 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1228 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28153_1228_53 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=26937 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28153_26937_25762 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_34169_1176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1200 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_35297_1200_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=34617 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_35297_34617_33442 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1197 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_44227_1197_22 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=43450 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_44227_43450_42275 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1192 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_74777_1192_17 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=73713 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_74777_73713_72538 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_78349_1176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_88877_1177_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_140201_1176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_186073_1177_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=186028 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_186073_186028_184853 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_318613_1177_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=318192 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_318613_318192_317017 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_431789_1176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=431649 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_431789_431649_430474 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_486497_1177_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=485700 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_486497_485700_484525 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1176 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_564329_1176_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=564001 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_564329_564001_562826 G hg ⟨f,hf⟩

end Signed39.Contraction
