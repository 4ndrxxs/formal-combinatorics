import Signed25Grid41Part0
import Signed25Grid41Part12
import Signed25Grid41Part24
import Signed25Grid41Part36
import Signed25Grid41Part48
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_41_25 : divisorGrid 41 25 314 qInputs_41_25 keep_41_25 := by
  intro d
  fin_cases d
  · exact grid41x25Case0
  · exact grid41x25Case1
  · exact grid41x25Case2
  · exact grid41x25Case3
  · exact grid41x25Case4
  · exact grid41x25Case5
  · exact grid41x25Case6
  · exact grid41x25Case7
  · exact grid41x25Case8
  · exact grid41x25Case9
  · exact grid41x25Case10
  · exact grid41x25Case11
  · exact grid41x25Case12
  · exact grid41x25Case13
  · exact grid41x25Case14
  · exact grid41x25Case15
  · exact grid41x25Case16
  · exact grid41x25Case17
  · exact grid41x25Case18
  · exact grid41x25Case19
  · exact grid41x25Case20
  · exact grid41x25Case21
  · exact grid41x25Case22
  · exact grid41x25Case23
  · exact grid41x25Case24
  · exact grid41x25Case25
  · exact grid41x25Case26
  · exact grid41x25Case27
  · exact grid41x25Case28
  · exact grid41x25Case29
  · exact grid41x25Case30
  · exact grid41x25Case31
  · exact grid41x25Case32
  · exact grid41x25Case33
  · exact grid41x25Case34
  · exact grid41x25Case35
  · exact grid41x25Case36
  · exact grid41x25Case37
  · exact grid41x25Case38
  · exact grid41x25Case39
  · exact grid41x25Case40
  · exact grid41x25Case41
  · exact grid41x25Case42
  · exact grid41x25Case43
  · exact grid41x25Case44
  · exact grid41x25Case45
  · exact grid41x25Case46
  · exact grid41x25Case47
  · exact grid41x25Case48
  · exact grid41x25Case49



private theorem frontier_mixed_1763_1033_8 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1763) : ¬∃ f : G → ℤ, IsSDS 1033 8 f :=
  abelian_short_linear G 41 43 31 0 5 10 1033 8 25 3 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2419_1609_584 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2419) : ¬∃ f : G → ℤ, IsSDS 1609 584 f :=
  abelian_short_linear G 41 59 31 0 5 10 1609 584 25 29 32 39
    ⟨⟨(-57),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2419_1650_625 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2419) : ¬∃ f : G → ℤ, IsSDS 1650 625 f :=
  abelian_short_linear G 41 59 31 0 5 10 1650 625 25 30 32 39
    ⟨⟨0,(-21),5,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3403_1738_713 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3403) : ¬∃ f : G → ℤ, IsSDS 1738 713 f :=
  abelian_short_linear G 41 83 31 0 5 10 1738 713 25 38 32 39
    ⟨⟨18,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3403_2025_1000 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3403) : ¬∃ f : G → ℤ, IsSDS 2025 1000 f :=
  abelian_short_linear G 41 83 31 0 5 10 2025 1000 25 45 32 39
    ⟨⟨35,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4223_1057_32 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4223) : ¬∃ f : G → ℤ, IsSDS 1057 32 f :=
  abelian_short_linear G 41 103 31 1 5 10 1057 32 25 9 32 39
    ⟨⟨(-24),(-23),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,150,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4387_1393_368 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4387) : ¬∃ f : G → ℤ, IsSDS 1393 368 f :=
  abelian_short_linear G 41 107 31 1 5 10 1393 368 25 31 32 39
    ⟨⟨21,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4387_3238_2213 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4387) : ¬∃ f : G → ℤ, IsSDS 3238 2213 f :=
  abelian_short_linear G 41 107 31 0 5 10 3238 2213 25 76 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4715_1105_80 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4715) : ¬∃ f : G → ℤ, IsSDS 1105 80 f :=
  abelian_short_linear G 41 115 31 1 5 10 1105 80 25 15 32 39
    ⟨⟨0,(-4715),375,134⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18450,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4715_4590_3565 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4715) : ¬∃ f : G → ℤ, IsSDS 4590 3565 f :=
  abelian_short_linear G 41 115 31 0 5 10 4590 3565 25 100 32 39
    ⟨⟨(-115),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5125_1033_8 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5125) : ¬∃ f : G → ℤ, IsSDS 1033 8 f :=
  abelian_short_linear G 41 125 31 1 5 10 1033 8 25 5 32 39
    ⟨⟨(-43050),(-820),375,161⟩,[43050,0,0,0,0,0,0,0,0,0,16400,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5125_1156_131 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5125) : ¬∃ f : G → ℤ, IsSDS 1156 131 f :=
  abelian_short_linear G 41 125 31 1 5 10 1156 131 25 20 32 39
    ⟨⟨0,(-61500),10000,1271⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,153750,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,153750,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5125_1320_295 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5125) : ¬∃ f : G → ℤ, IsSDS 1320 295 f :=
  abelian_short_linear G 41 125 31 1 5 10 1320 295 25 30 32 39
    ⟨⟨0,(-615),150,7⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4100,0,0,0,0,4100],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5125_3985_2960 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5125) : ¬∃ f : G → ℤ, IsSDS 3985 2960 f :=
  abelian_short_linear G 41 125 31 0 5 10 3985 2960 25 95 32 39
    ⟨⟨(-12500),123,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5125_4641_3616 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5125) : ¬∃ f : G → ℤ, IsSDS 4641 3616 f :=
  abelian_short_linear G 41 125 31 0 5 10 4641 3616 25 105 32 39
    ⟨⟨(-125),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5207_1398_373 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5207) : ¬∃ f : G → ℤ, IsSDS 1398 373 f :=
  abelian_short_linear G 41 127 31 0 5 10 1398 373 25 34 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5207_3817_2792 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5207) : ¬∃ f : G → ℤ, IsSDS 3817 2792 f :=
  abelian_short_linear G 41 127 31 0 5 10 3817 2792 25 93 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5371_1150_125 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5371) : ¬∃ f : G → ℤ, IsSDS 1150 125 f :=
  abelian_short_linear G 41 131 31 1 5 10 1150 125 25 20 32 39
    ⟨⟨0,(-3485),350,69⟩,[0,0,0,0,0,0,0,0,0,0,2050,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18450,0,0,0,0,10250,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5371_4881_3856 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5371) : ¬∃ f : G → ℤ, IsSDS 4881 3856 f :=
  abelian_short_linear G 41 131 31 0 5 10 4881 3856 25 111 32 39
    ⟨⟨(-131),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5699_1026_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5699) : ¬∃ f : G → ℤ, IsSDS 1026 1 f :=
  abelian_short_linear G 41 139 31 2 5 10 1026 1 25 2 32 39
    ⟨⟨(-2500),0,61,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6683_1050_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6683) : ¬∃ f : G → ℤ, IsSDS 1050 25 f :=
  abelian_short_linear G 41 163 31 2 5 10 1050 25 25 10 32 39
    ⟨⟨0,(-1640),125,43⟩,[0,0,0,0,0,0,0,0,0,0,4100,0,0,0,0,2050,0,0,0,0,4100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11603_1062_37 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11603) : ¬∃ f : G → ℤ, IsSDS 1062 37 f :=
  abelian_short_linear G 41 283 31 3 5 10 1062 37 25 16 32 39
    ⟨⟨(-11152),(-8241),375,268⟩,[0,0,0,0,0,0,8200,0,0,0,0,0,0,0,0,0,36900,0,0,0,0,26650,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_11603_11353_10328 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=11603) : ¬∃ f : G → ℤ, IsSDS 11353 10328 f :=
  abelian_short_linear G 41 283 31 0 5 10 11353 10328 25 267 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23575_1041_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23575) : ¬∃ f : G → ℤ, IsSDS 1041 16 f :=
  abelian_short_linear G 41 575 31 5 5 10 1041 16 25 15 32 39
    ⟨⟨0,(-30750),1250,943⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23575_23386_22361 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23575) : ¬∃ f : G → ℤ, IsSDS 23386 22361 f :=
  abelian_short_linear G 41 575 31 0 5 10 23386 22361 25 560 32 39
    ⟨⟨(-575),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_25871_1026_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=25871) : ¬∃ f : G → ℤ, IsSDS 1026 1 f :=
  abelian_short_linear G 41 631 31 8 5 10 1026 1 25 4 32 39
    ⟨⟨(-1560),(-120),37,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_26855_1050_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=26855) : ¬∃ f : G → ℤ, IsSDS 1050 25 f :=
  abelian_short_linear G 41 655 31 2 5 10 1050 25 25 20 32 39
    ⟨⟨0,(-16810),525,443⟩,[0,0,0,0,0,0,0,0,0,0,4100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41000,0,0,0,0,61500,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_26855_26265_25240 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=26855) : ¬∃ f : G → ℤ, IsSDS 26265 25240 f :=
  abelian_short_linear G 41 655 31 0 5 10 26265 25240 25 635 32 39
    ⟨⟨(-655),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_27757_1057_32 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=27757) : ¬∃ f : G → ℤ, IsSDS 1057 32 f :=
  abelian_short_linear G 41 677 31 1 5 10 1057 32 25 23 32 39
    ⟨⟨(-90),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_27757_26928_25903 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=27757) : ¬∃ f : G → ℤ, IsSDS 26928 25903 f :=
  abelian_short_linear G 41 677 31 0 5 10 26928 25903 25 654 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_30299_1041_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=30299) : ¬∃ f : G → ℤ, IsSDS 1041 16 f :=
  abelian_short_linear G 41 739 31 4 5 10 1041 16 25 17 32 39
    ⟨⟨(-70602),(-7093),525,172⟩,[0,0,38950,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_30299_29946_28921 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=30299) : ¬∃ f : G → ℤ, IsSDS 29946 28921 f :=
  abelian_short_linear G 41 739 31 0 5 10 29946 28921 25 722 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_33415_1030_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=33415) : ¬∃ f : G → ℤ, IsSDS 1030 5 f :=
  abelian_short_linear G 41 815 31 7 5 10 1030 5 25 10 32 39
    ⟨⟨(-339680),(-14861),3495,0⟩,[339680,0,0,0,0,148610,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_35383_1033_8 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=35383) : ¬∃ f : G → ℤ, IsSDS 1033 8 f :=
  abelian_short_linear G 41 863 31 6 5 10 1033 8 25 13 32 39
    ⟨⟨(-76834),(-9799),675,134⟩,[0,0,0,32800,0,0,0,0,14350,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_35383_35350_34325 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=35383) : ¬∃ f : G → ℤ, IsSDS 35350 34325 f :=
  abelian_short_linear G 41 863 31 0 5 10 35350 34325 25 850 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_59491_1026_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=59491) : ¬∃ f : G → ℤ, IsSDS 1026 1 f :=
  abelian_short_linear G 41 1451 31 9 5 10 1026 1 25 6 32 39
    ⟨⟨(-28089264),(-8192702),611700,191675⟩,[0,0,0,0,0,0,25079700,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_75727_1033_8 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=75727) : ¬∃ f : G → ℤ, IsSDS 1033 8 f :=
  abelian_short_linear G 41 1847 31 3 5 10 1033 8 25 19 32 39
    ⟨⟨4,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_75727_75202_74177 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=75727) : ¬∃ f : G → ℤ, IsSDS 75202 74177 f :=
  abelian_short_linear G 41 1847 31 0 5 10 75202 74177 25 1828 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_134275_1030_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=134275) : ¬∃ f : G → ℤ, IsSDS 1030 5 f :=
  abelian_short_linear G 41 3275 31 2 5 10 1030 5 25 20 32 39
    ⟨⟨5,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_134275_133665_132640 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=134275) : ¬∃ f : G → ℤ, IsSDS 133665 132640 f :=
  abelian_short_linear G 41 3275 31 0 5 10 133665 132640 25 3255 32 39
    ⟨⟨(-3275),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_167075_1026_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=167075) : ¬∃ f : G → ℤ, IsSDS 1026 1 f :=
  abelian_short_linear G 41 4075 31 7 5 10 1026 1 25 10 32 39
    ⟨⟨0,(-410),25,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_241039_1026_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=241039) : ¬∃ f : G → ℤ, IsSDS 1026 1 f :=
  abelian_short_linear G 41 5879 31 6 5 10 1026 1 25 12 32 39
    ⟨⟨(-328),(-574),20,9⟩,[0,0,0,0,0,0,0,205,0,0,0,0,0,0,0,0,0,1025,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_328451_1026_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=328451) : ¬∃ f : G → ℤ, IsSDS 1026 1 f :=
  abelian_short_linear G 41 8011 31 5 5 10 1026 1 25 14 32 39
    ⟨⟨0,0,33,(-40)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_328451_328329_327304 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=328451) : ¬∃ f : G → ℤ, IsSDS 328329 327304 f :=
  abelian_short_linear G 41 8011 31 0 5 10 328329 327304 25 7997 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_543619_1026_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=543619) : ¬∃ f : G → ℤ, IsSDS 1026 1 f :=
  abelian_short_linear G 41 13259 31 3 5 10 1026 1 25 18 32 39
    ⟨⟨8,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_543619_543169_542144 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=543619) : ¬∃ f : G → ℤ, IsSDS 543169 542144 f :=
  abelian_short_linear G 41 13259 31 0 5 10 543169 542144 25 13241 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_671375_1026_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=671375) : ¬∃ f : G → ℤ, IsSDS 1026 1 f :=
  abelian_short_linear G 41 16375 31 2 5 10 1026 1 25 20 32 39
    ⟨⟨5,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_671375_670761_669736 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=671375) : ¬∃ f : G → ℤ, IsSDS 670761 669736 f :=
  abelian_short_linear G 41 16375 31 0 5 10 670761 669736 25 16355 32 39
    ⟨⟨(-16375),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_812579_1026_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=812579) : ¬∃ f : G → ℤ, IsSDS 1026 1 f :=
  abelian_short_linear G 41 19819 31 1 5 10 1026 1 25 22 32 39
    ⟨⟨2,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_812579_811801_810776 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=812579) : ¬∃ f : G → ℤ, IsSDS 811801 810776 f :=
  abelian_short_linear G 41 19819 31 0 5 10 811801 810776 25 19797 32 39
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_41_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=41*m)
    (hm : 41 < m) (hn : k-l=(41:ℤ)*25) : False := by
  let : Fact (Nat.Prime 41) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_41_25
  simp only [keep_41_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1033 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1763_1033_8 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1609 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2419_1609_584 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1650 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2419_1650_625 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1738 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3403_1738_713 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3403_2025_1000 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1057 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4223_1057_32 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1393 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4387_1393_368 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3238 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4387_3238_2213 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1105 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4715_1105_80 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4590 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4715_4590_3565 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1033 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5125_1033_8 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1156 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5125_1156_131 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1320 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5125_1320_295 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3985 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5125_3985_2960 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4641 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5125_4641_3616 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1398 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5207_1398_373 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3817 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5207_3817_2792 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1150 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5371_1150_125 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4881 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5371_4881_3856 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1026 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5699_1026_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1050 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6683_1050_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1062 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11603_1062_37 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=11353 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_11603_11353_10328 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1041 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23575_1041_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=23386 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23575_23386_22361 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1026 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_25871_1026_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1050 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_26855_1050_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=26265 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_26855_26265_25240 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1057 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_27757_1057_32 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=26928 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_27757_26928_25903 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1041 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_30299_1041_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=29946 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_30299_29946_28921 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1030 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_33415_1030_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1033 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_35383_1033_8 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=35350 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_35383_35350_34325 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1026 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_59491_1026_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1033 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_75727_1033_8 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=75202 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_75727_75202_74177 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1030 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_134275_1030_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=133665 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_134275_133665_132640 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1026 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_167075_1026_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1026 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_241039_1026_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1026 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_328451_1026_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=328329 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_328451_328329_327304 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1026 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_543619_1026_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=543169 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_543619_543169_542144 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1026 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_671375_1026_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=670761 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_671375_670761_669736 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1026 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_812579_1026_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=811801 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_812579_811801_810776 G hg ⟨f,hf⟩

end Signed39.Contraction
