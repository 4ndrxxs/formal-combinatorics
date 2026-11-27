import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_31_16 : ℕ → Option QuotientInput
  | 41 => some ⟨41,31,5,0,16⟩
  | 109 => some ⟨109,31,27,0,16⟩
  | 123 => some ⟨41,31,5,0,16⟩
  | 257 => some ⟨257,31,64,0,16⟩
  | 771 => some ⟨257,31,64,0,16⟩
  | _ => none

private def keep_31_16 : List (ℕ × ℤ) := [(33,23),(33,240),(33,271),(43,288),(43,381),(45,83),(45,176),(45,579),(45,796),(55,20),(55,144),(55,857),(69,11),(75,149),(75,1296),(83,45),(83,1936),(99,80),(99,2157),(101,60),(101,2323),(139,32),(139,3597),(165,48),(165,4171),(167,9),(249,15),(249,7052),(253,3),(263,1),(271,33),(271,7380),(275,4),(303,20),(303,8545),(415,9),(415,12192),(495,16),(495,14369),(499,5),(499,14916),(501,3),(505,12),(505,14799),(747,5),(747,22480),(759,1),(1245,3),(1245,37916),(1503,1),(1515,4),(1515,46101),(1741,3),(1741,53168),(2495,1),(2495,76788),(3735,1),(3735,115104),(5223,1),(5223,161108),(6959,1),(6959,214800)]

private theorem grid_31_16 : divisorGrid 31 16 173 qInputs_31_16 keep_31_16 := by decide +kernel

private theorem frontier_mixed_1023_519_23 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1023) : ¬∃ f : G → ℤ, IsSDS 519 23 f :=
  abelian_short_linear G 31 33 21 0 1 0 519 23 16 5 1 1
    ⟨⟨0,(-4),1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1023_736_240 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1023) : ¬∃ f : G → ℤ, IsSDS 736 240 f :=
  abelian_short_linear G 31 33 21 0 1 0 736 240 16 16 1 1
    ⟨⟨0,(-383780),77376,9285⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1023_767_271 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1023) : ¬∃ f : G → ℤ, IsSDS 767 271 f :=
  abelian_short_linear G 31 33 21 0 1 0 767 271 16 17 1 1
    ⟨⟨0,(-383780),77376,9285⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1333_784_288 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1333) : ¬∃ f : G → ℤ, IsSDS 784 288 f :=
  abelian_short_linear G 31 43 21 0 1 0 784 288 16 20 1 1
    ⟨⟨17,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1333_877_381 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1333) : ¬∃ f : G → ℤ, IsSDS 877 381 f :=
  abelian_short_linear G 31 43 21 0 1 0 877 381 16 23 1 1
    ⟨⟨(-34),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1395_579_83 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1395) : ¬∃ f : G → ℤ, IsSDS 579 83 f :=
  abelian_short_linear G 31 45 21 0 1 0 579 83 16 11 1 1
    ⟨⟨0,(-93),20,3⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1395_672_176 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1395) : ¬∃ f : G → ℤ, IsSDS 672 176 f :=
  abelian_short_linear G 31 45 21 0 1 0 672 176 16 16 1 1
    ⟨⟨0,0,12952775,(-6236494)⟩,[0,0,0,0,0,0,0,0,0,0,0,327183230,0,0,0,0,1130269340,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1395_1075_579 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1395) : ¬∃ f : G → ℤ, IsSDS 1075 579 f :=
  abelian_short_linear G 31 45 21 0 1 0 1075 579 16 29 1 1
    ⟨⟨(-495),(-6),17,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1395_1292_796 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1395) : ¬∃ f : G → ℤ, IsSDS 1292 796 f :=
  abelian_short_linear G 31 45 21 0 1 0 1292 796 16 34 1 1
    ⟨⟨900,9,(-29),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1705_516_20 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1705) : ¬∃ f : G → ℤ, IsSDS 516 20 f :=
  abelian_short_linear G 31 55 21 1 1 0 516 20 16 6 1 1
    ⟨⟨0,(-682),56,39⟩,[0,0,0,0,0,0,0,0,496,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1705_640_144 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1705) : ¬∃ f : G → ℤ, IsSDS 640 144 f :=
  abelian_short_linear G 31 55 21 0 1 0 640 144 16 16 1 1
    ⟨⟨0,(-372),80,7⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1116,0,0,0,0,1581,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1705_1353_857 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1705) : ¬∃ f : G → ℤ, IsSDS 1353 857 f :=
  abelian_short_linear G 31 55 21 0 1 0 1353 857 16 39 1 1
    ⟨⟨(-55),(-1),2,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2139_507_11 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2139) : ¬∃ f : G → ℤ, IsSDS 507 11 f :=
  abelian_short_linear G 31 69 21 1 1 0 507 11 16 5 1 1
    ⟨⟨0,(-13711548),1236560,813285⟩,[0,0,0,0,0,0,0,0,0,0,16217960,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2325_645_149 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2325) : ¬∃ f : G → ℤ, IsSDS 645 149 f :=
  abelian_short_linear G 31 75 21 0 1 0 645 149 16 19 1 1
    ⟨⟨0,(-4898),1260,101⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9672,0,0,0,0,0,5952,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2325_1792_1296 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2325) : ¬∃ f : G → ℤ, IsSDS 1792 1296 f :=
  abelian_short_linear G 31 75 21 0 1 0 1792 1296 16 56 1 1
    ⟨⟨(-75),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2573_541_45 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2573) : ¬∃ f : G → ℤ, IsSDS 541 45 f :=
  abelian_short_linear G 31 83 21 1 1 0 541 45 16 11 1 1
    ⟨⟨0,(-4526),483,163⟩,[0,0,0,0,0,0,0,0,0,0,3844,4464,1860,0,0,4650,0,372,8370,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2573_2432_1936 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2573) : ¬∃ f : G → ℤ, IsSDS 2432 1936 f :=
  abelian_short_linear G 31 83 21 0 1 0 2432 1936 16 72 1 1
    ⟨⟨(-1162),(-9),23,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3069_576_80 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3069) : ¬∃ f : G → ℤ, IsSDS 576 80 f :=
  abelian_short_linear G 31 99 21 1 1 0 576 80 16 16 1 1
    ⟨⟨0,(-1085),125,36⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1550,0,2666,1116,744,1550,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3069_2653_2157 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3069) : ¬∃ f : G → ℤ, IsSDS 2653 2157 f :=
  abelian_short_linear G 31 99 21 0 1 0 2653 2157 16 83 1 1
    ⟨⟨(-86),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3131_556_60 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3131) : ¬∃ f : G → ℤ, IsSDS 556 60 f :=
  abelian_short_linear G 31 101 21 1 1 0 556 60 16 14 1 1
    ⟨⟨0,(-1395),182,47⟩,[0,0,0,0,0,0,0,0,0,558,0,0,0,0,3038,0,0,0,0,620,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3131_2819_2323 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3131) : ¬∃ f : G → ℤ, IsSDS 2819 2323 f :=
  abelian_short_linear G 31 101 21 0 1 0 2819 2323 16 87 1 1
    ⟨⟨(-101),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4309_528_32 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4309) : ¬∃ f : G → ℤ, IsSDS 528 32 f :=
  abelian_short_linear G 31 139 21 2 1 0 528 32 16 12 1 1
    ⟨⟨0,(-5394),880,117⟩,[0,0,0,0,0,0,0,0,0,0,0,12617,0,0,0,0,0,0,0,0,1240,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4309_4093_3597 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4309) : ¬∃ f : G → ℤ, IsSDS 4093 3597 f :=
  abelian_short_linear G 31 139 21 0 1 0 4093 3597 16 127 1 1
    ⟨⟨(-139),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5115_544_48 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5115) : ¬∃ f : G → ℤ, IsSDS 544 48 f :=
  abelian_short_linear G 31 165 21 0 1 0 544 48 16 16 1 1
    ⟨⟨0,(-2019),823,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5115_4667_4171 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5115) : ¬∃ f : G → ℤ, IsSDS 4667 4171 f :=
  abelian_short_linear G 31 165 21 0 1 0 4667 4171 16 149 1 1
    ⟨⟨(-165),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5177_505_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5177) : ¬∃ f : G → ℤ, IsSDS 505 9 f :=
  abelian_short_linear G 31 167 21 2 1 0 505 9 16 7 1 1
    ⟨⟨0,(-4247),195,224⟩,[0,0,0,0,0,620,0,3348,2480,0,0,3038,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7719_511_15 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7719) : ¬∃ f : G → ℤ, IsSDS 511 15 f :=
  abelian_short_linear G 31 249 21 2 1 0 511 15 16 11 1 1
    ⟨⟨(-5084),(-279),76,17⟩,[5084,558,558,372,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7719_7548_7052 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7719) : ¬∃ f : G → ℤ, IsSDS 7548 7052 f :=
  abelian_short_linear G 31 249 21 0 1 0 7548 7052 16 238 1 1
    ⟨⟨2490,13,(-23),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7843_499_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7843) : ¬∃ f : G → ℤ, IsSDS 499 3 f :=
  abelian_short_linear G 31 253 21 4 1 0 499 3 16 5 1 1
    ⟨⟨(-17050),(-4743),690,79⟩,[17050,0,0,3658,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8153_497_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8153) : ¬∃ f : G → ℤ, IsSDS 497 1 f :=
  abelian_short_linear G 31 263 21 4 1 0 497 1 16 3 1 1
    ⟨⟨(-36494874),(-611847),804573,(-46438)⟩,[36494874,0,0,0,0,6118470,0,0,0,1511622,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8401_529_33 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8401) : ¬∃ f : G → ℤ, IsSDS 529 33 f :=
  abelian_short_linear G 31 271 21 0 1 0 529 33 16 17 1 1
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8401_7876_7380 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8401) : ¬∃ f : G → ℤ, IsSDS 7876 7380 f :=
  abelian_short_linear G 31 271 21 0 1 0 7876 7380 16 254 1 1
    ⟨⟨(-271),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8525_500_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8525) : ¬∃ f : G → ℤ, IsSDS 500 4 f :=
  abelian_short_linear G 31 275 21 4 1 0 500 4 16 6 1 1
    ⟨⟨(-2103257520),(-38439240),34387080,0⟩,[2103257520,0,0,0,307559681,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9393_516_20 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9393) : ¬∃ f : G → ℤ, IsSDS 516 20 f :=
  abelian_short_linear G 31 303 21 1 1 0 516 20 16 14 1 1
    ⟨⟨0,(-14151606),254981,638644⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,13097763,12796665,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9393_9041_8545 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9393) : ¬∃ f : G → ℤ, IsSDS 9041 8545 f :=
  abelian_short_linear G 31 303 21 0 1 0 9041 8545 16 289 1 1
    ⟨⟨(-303),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12865_505_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12865) : ¬∃ f : G → ℤ, IsSDS 505 9 f :=
  abelian_short_linear G 31 415 21 2 1 0 505 9 16 11 1 1
    ⟨⟨(-3478051467),(-418866714),40637366,11461527⟩,[3478051467,837733428,2156850990,0,1556683758,0,0,118783098,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,481384134,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12865_12688_12192 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12865) : ¬∃ f : G → ℤ, IsSDS 12688 12192 f :=
  abelian_short_linear G 31 415 21 0 1 0 12688 12192 16 404 1 1
    ⟨⟨(-415),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15345_512_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15345) : ¬∃ f : G → ℤ, IsSDS 512 16 f :=
  abelian_short_linear G 31 495 21 0 1 0 512 16 16 16 1 1
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15345_14865_14369 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15345) : ¬∃ f : G → ℤ, IsSDS 14865 14369 f :=
  abelian_short_linear G 31 495 21 0 1 0 14865 14369 16 479 1 1
    ⟨⟨(-495),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15469_501_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15469) : ¬∃ f : G → ℤ, IsSDS 501 5 f :=
  abelian_short_linear G 31 499 21 3 1 0 501 5 16 9 1 1
    ⟨⟨(-19251),(-124),231,(-46)⟩,[19251,248,279,5022,155,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4278,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15469_15412_14916 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15469) : ¬∃ f : G → ℤ, IsSDS 15412 14916 f :=
  abelian_short_linear G 31 499 21 0 1 0 15412 14916 16 490 1 1
    ⟨⟨(-499),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15531_499_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15531) : ¬∃ f : G → ℤ, IsSDS 499 3 f :=
  abelian_short_linear G 31 501 21 4 1 0 499 3 16 7 1 1
    ⟨⟨(-108500),(-9021),2415,(-328)⟩,[108500,0,36084,44330,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15655_508_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15655) : ¬∃ f : G → ℤ, IsSDS 508 12 f :=
  abelian_short_linear G 31 505 21 1 1 0 508 12 16 14 1 1
    ⟨⟨0,(-81),35,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15655_15295_14799 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15655) : ¬∃ f : G → ℤ, IsSDS 15295 14799 f :=
  abelian_short_linear G 31 505 21 0 1 0 15295 14799 16 491 1 1
    ⟨⟨(-505),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23157_501_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23157) : ¬∃ f : G → ℤ, IsSDS 501 5 f :=
  abelian_short_linear G 31 747 21 2 1 0 501 5 16 11 1 1
    ⟨⟨0,0,2019,(-5000)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23157_22976_22480 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23157) : ¬∃ f : G → ℤ, IsSDS 22976 22480 f :=
  abelian_short_linear G 31 747 21 0 1 0 22976 22480 16 736 1 1
    ⟨⟨(-747),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23529_497_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23529) : ¬∃ f : G → ℤ, IsSDS 497 1 f :=
  abelian_short_linear G 31 759 21 5 1 0 497 1 16 5 1 1
    ⟨⟨(-10845),(-723),175,0⟩,[10845,0,2892,0,0,0,0,0,0,0,0,2892,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_38595_499_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=38595) : ¬∃ f : G → ℤ, IsSDS 499 3 f :=
  abelian_short_linear G 31 1245 21 2 1 0 499 3 16 11 1 1
    ⟨⟨0,0,25,(-129)⟩,[0,0,0,0,0,0,744,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_38595_38412_37916 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=38595) : ¬∃ f : G → ℤ, IsSDS 38412 37916 f :=
  abelian_short_linear G 31 1245 21 0 1 0 38412 37916 16 1234 1 1
    ⟨⟨(-1245),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_46593_497_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=46593) : ¬∃ f : G → ℤ, IsSDS 497 1 f :=
  abelian_short_linear G 31 1503 21 4 1 0 497 1 16 7 1 1
    ⟨⟨(-169220832),(-4573536),2152080,0⟩,[169220832,0,64791760,27441216,0,0,0,0,0,11433840,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,46496835,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_46965_500_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=46965) : ¬∃ f : G → ℤ, IsSDS 500 4 f :=
  abelian_short_linear G 31 1515 21 1 1 0 500 4 16 14 1 1
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_46965_46597_46101 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=46965) : ¬∃ f : G → ℤ, IsSDS 46597 46101 f :=
  abelian_short_linear G 31 1515 21 0 1 0 46597 46101 16 1501 1 1
    ⟨⟨(-1515),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_53971_499_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=53971) : ¬∃ f : G → ℤ, IsSDS 499 3 f :=
  abelian_short_linear G 31 1741 21 1 1 0 499 3 16 13 1 1
    ⟨⟨1,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_53971_53664_53168 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=53971) : ¬∃ f : G → ℤ, IsSDS 53664 53168 f :=
  abelian_short_linear G 31 1741 21 0 1 0 53664 53168 16 1728 1 1
    ⟨⟨(-1741),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_77345_497_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=77345) : ¬∃ f : G → ℤ, IsSDS 497 1 f :=
  abelian_short_linear G 31 2495 21 3 1 0 497 1 16 9 1 1
    ⟨⟨0,0,9,(-13)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_77345_77284_76788 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=77345) : ¬∃ f : G → ℤ, IsSDS 77284 76788 f :=
  abelian_short_linear G 31 2495 21 0 1 0 77284 76788 16 2486 1 1
    ⟨⟨(-2495),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_115785_497_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=115785) : ¬∃ f : G → ℤ, IsSDS 497 1 f :=
  abelian_short_linear G 31 3735 21 2 1 0 497 1 16 11 1 1
    ⟨⟨0,0,1,(-91)⟩,[0,0,310,744,1364,2170,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2170,1364,744,310,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_115785_115600_115104 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=115785) : ¬∃ f : G → ℤ, IsSDS 115600 115104 f :=
  abelian_short_linear G 31 3735 21 0 1 0 115600 115104 16 3724 1 1
    ⟨⟨(-3735),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_161913_497_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=161913) : ¬∃ f : G → ℤ, IsSDS 497 1 f :=
  abelian_short_linear G 31 5223 21 1 1 0 497 1 16 13 1 1
    ⟨⟨0,0,1,(-91)⟩,[0,0,310,744,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,744,310,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_161913_161604_161108 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=161913) : ¬∃ f : G → ℤ, IsSDS 161604 161108 f :=
  abelian_short_linear G 31 5223 21 0 1 0 161604 161108 16 5210 1 1
    ⟨⟨(-5223),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_215729_497_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=215729) : ¬∃ f : G → ℤ, IsSDS 497 1 f :=
  abelian_short_linear G 31 6959 21 0 1 0 497 1 16 15 1 1
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_215729_215296_214800 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=215729) : ¬∃ f : G → ℤ, IsSDS 215296 214800 f :=
  abelian_short_linear G 31 6959 21 0 1 0 215296 214800 16 6944 1 1
    ⟨⟨(-6959),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_31_16_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=31*m)
    (hm : 31 < m) (hn : k-l=(31:ℤ)*16) : False := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  have row := endpoint_case (s:=16) hf hg hn (by decide) hm grid_31_16
  simp only [keep_31_16,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=519 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1023_519_23 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=736 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1023_736_240 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=767 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1023_767_271 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=784 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1333_784_288 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=877 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1333_877_381 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=579 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1395_579_83 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=672 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1395_672_176 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1075 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1395_1075_579 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1292 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1395_1292_796 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=516 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1705_516_20 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=640 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1705_640_144 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1353 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1705_1353_857 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=507 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2139_507_11 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=645 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2325_645_149 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1792 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2325_1792_1296 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=541 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2573_541_45 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2432 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2573_2432_1936 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=576 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3069_576_80 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2653 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3069_2653_2157 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=556 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3131_556_60 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2819 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3131_2819_2323 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=528 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4309_528_32 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4093 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4309_4093_3597 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=544 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5115_544_48 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4667 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5115_4667_4171 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=505 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5177_505_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=511 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7719_511_15 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7548 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7719_7548_7052 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=499 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7843_499_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=497 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8153_497_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=529 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8401_529_33 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7876 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8401_7876_7380 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=500 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8525_500_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=516 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9393_516_20 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=9041 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9393_9041_8545 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=505 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12865_505_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=12688 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12865_12688_12192 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=512 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15345_512_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=14865 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15345_14865_14369 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=501 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15469_501_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=15412 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15469_15412_14916 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=499 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15531_499_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=508 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15655_508_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=15295 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15655_15295_14799 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=501 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23157_501_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=22976 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23157_22976_22480 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=497 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23529_497_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=499 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_38595_499_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=38412 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_38595_38412_37916 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=497 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_46593_497_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=500 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_46965_500_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=46597 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_46965_46597_46101 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=499 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_53971_499_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=53664 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_53971_53664_53168 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=497 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_77345_497_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=77284 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_77345_77284_76788 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=497 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_115785_497_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=115600 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_115785_115600_115104 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=497 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_161913_497_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=161604 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_161913_161604_161108 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=497 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_215729_497_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=215296 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_215729_215296_214800 G hg ⟨f,hf⟩

end Signed39.Contraction
