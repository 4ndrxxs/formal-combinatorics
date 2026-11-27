import Signed25Grid3Part0
import Signed25Grid3Part12
import Signed25Grid3Part24
import Signed25Grid3Part36
import Signed25Grid3Part48
import Signed25Fibre537W88
import SignedLong327
import SignedLong177
import SignedLong141
import SignedLong213
import SignedLong393
import SignedLong393
import SignedLong249
import SignedLong321
import Signed25Fibre1263W77
import SignedLong141
import SignedLong177
import SignedLong213
import SignedAlmostBinary
import Signed25Fibre537W457
import Signed25Fibre501W76
import SignedLong321
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_3_25 : divisorGrid 3 25 85 qInputs_3_25 keep_3_25 := by
  intro d
  fin_cases d
  · exact grid3x25Case0
  · exact grid3x25Case1
  · exact grid3x25Case2
  · exact grid3x25Case3
  · exact grid3x25Case4
  · exact grid3x25Case5
  · exact grid3x25Case6
  · exact grid3x25Case7
  · exact grid3x25Case8
  · exact grid3x25Case9
  · exact grid3x25Case10
  · exact grid3x25Case11
  · exact grid3x25Case12
  · exact grid3x25Case13
  · exact grid3x25Case14
  · exact grid3x25Case15
  · exact grid3x25Case16
  · exact grid3x25Case17
  · exact grid3x25Case18
  · exact grid3x25Case19
  · exact grid3x25Case20
  · exact grid3x25Case21
  · exact grid3x25Case22
  · exact grid3x25Case23
  · exact grid3x25Case24
  · exact grid3x25Case25
  · exact grid3x25Case26
  · exact grid3x25Case27
  · exact grid3x25Case28
  · exact grid3x25Case29
  · exact grid3x25Case30
  · exact grid3x25Case31
  · exact grid3x25Case32
  · exact grid3x25Case33
  · exact grid3x25Case34
  · exact grid3x25Case35
  · exact grid3x25Case36
  · exact grid3x25Case37
  · exact grid3x25Case38
  · exact grid3x25Case39
  · exact grid3x25Case40
  · exact grid3x25Case41
  · exact grid3x25Case42
  · exact grid3x25Case43
  · exact grid3x25Case44
  · exact grid3x25Case45
  · exact grid3x25Case46
  · exact grid3x25Case47
  · exact grid3x25Case48
  · exact grid3x25Case49



private theorem frontier_mixed_1263_1238_1163 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1263) : ¬∃ f : G → ℤ, IsSDS 1238 1163 f :=
  abelian_short_linear G 3 421 7 4 5 1 1238 1163 25 404 2 33
    ⟨⟨(-1),0,0,0⟩,[1,1,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1587_77_2 : List RowType := [(14,22),(14,28),(14,34),(19,25),(19,31),(19,37),(24,24),(24,30),(24,36),(24,42)]
private def stage_0_frontier_mixed_1587_77_2 : Stage := [
  ((14,22),⟨⟨(-140112),0,0,0⟩,[0,0,918],1⟩),
  ((14,28),⟨⟨(-140112),0,0,0⟩,[0,0,918],1⟩),
  ((14,34),⟨⟨(-24),0,1,0⟩,[0,0,2],0⟩),
  ((19,25),⟨⟨(-171912),0,0,0⟩,[0,92448,0],1⟩),
  ((19,31),⟨⟨(-171912),0,0,0⟩,[0,92448,0],1⟩),
  ((19,37),⟨⟨(-22),0,1,0⟩,[0,0,0],0⟩),
  ((24,24),⟨⟨(-140112),0,0,0⟩,[0,0,0],1⟩),
  ((24,30),⟨⟨(-140112),0,0,0⟩,[0,0,0],1⟩),
  ((24,36),⟨⟨(-22),0,1,0⟩,[0,0,0],0⟩),
  ((24,42),⟨⟨(-22),0,1,0⟩,[0,0,0],0⟩)]
private theorem frontier_mixed_1587_77_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1587) : ¬∃ f : G → ℤ, IsSDS 77 2 f :=
  abelian_short_mixed G 3 529 7 3 5 1 77 2 25 19 2 33 353 2
    types_frontier_mixed_1587_77_2 [stage_0_frontier_mixed_1587_77_2] ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1587_1550_1475 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1587) : ¬∃ f : G → ℤ, IsSDS 1550 1475 f :=
  abelian_short_linear G 3 529 7 3 5 1 1550 1475 25 510 2 33
    ⟨⟨505,(-1),0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1689_76_1 : List RowType := [(9,15),(9,21),(9,27),(9,33),(9,39),(14,20),(14,26),(14,32),(14,38),(14,44),(19,23),(19,29),(19,35),(19,41),(19,47),(19,53)]
private def stage_0_frontier_mixed_1689_76_1 : Stage := [
  ((9,39),⟨⟨(-20),0,1,0⟩,[5,0,0],0⟩),
  ((14,20),⟨⟨(-65646),0,0,0⟩,[0,0,0],1⟩),
  ((14,26),⟨⟨(-65646),0,0,0⟩,[0,0,0],1⟩),
  ((14,44),⟨⟨(-39),(-4),5,0⟩,[0,0,0],0⟩),
  ((19,23),⟨⟨(-86526),0,0,0⟩,[0,0,0],1⟩),
  ((19,29),⟨⟨(-86526),0,0,0⟩,[0,0,0],1⟩),
  ((19,47),⟨⟨(-15),0,1,0⟩,[0,0,0],0⟩),
  ((19,53),⟨⟨(-15),0,1,0⟩,[0,0,0],0⟩)]
private theorem frontier_mixed_1689_76_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1689) : ¬∃ f : G → ℤ, IsSDS 76 1 f :=
  abelian_short_mixed G 3 563 7 5 5 1 76 1 25 14 2 33 188 1
    types_frontier_mixed_1689_76_1 [stage_0_frontier_mixed_1689_76_1] ⟨⟨(-226320),0,74497,(-10902)⟩,[0,1593588,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1689_1681_1606 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1689) : ¬∃ f : G → ℤ, IsSDS 1681 1606 f :=
  abelian_short_linear G 3 563 7 3 5 1 1681 1606 25 549 2 33
    ⟨⟨(-554),1,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1947_77_2 : List RowType := [(16,22),(16,28),(21,21),(21,27),(21,33),(26,28),(26,34),(26,40)]
private def stage_0_frontier_mixed_1947_77_2 : Stage := [
  ((16,22),⟨⟨(-180432),0,0,0⟩,[0,0,0],1⟩),
  ((16,28),⟨⟨(-180432),0,0,0⟩,[0,0,0],1⟩),
  ((21,21),⟨⟨(-180432),0,0,0⟩,[0,0,0],1⟩),
  ((21,27),⟨⟨(-180432),0,0,0⟩,[0,0,0],1⟩),
  ((21,33),⟨⟨(-1284),0,70,(-1)⟩,[255,0,0],0⟩),
  ((26,28),⟨⟨(-254982),0,0,0⟩,[0,0,237702],1⟩),
  ((26,34),⟨⟨(-2495598),58128,0,0⟩,[0,0,897870],5⟩),
  ((26,40),⟨⟨(-21),0,1,0⟩,[0,0,0],0⟩)]
private theorem frontier_mixed_1947_77_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1947) : ¬∃ f : G → ℤ, IsSDS 77 2 f :=
  abelian_short_mixed G 3 649 7 2 5 1 77 2 25 21 2 33 433 2
    types_frontier_mixed_1947_77_2 [stage_0_frontier_mixed_1947_77_2] ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1947_1898_1823 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1947) : ¬∃ f : G → ℤ, IsSDS 1898 1823 f :=
  abelian_short_linear G 3 649 7 2 5 1 1898 1823 25 628 2 33
    ⟨⟨(-391244),1251,0,(-1)⟩,[0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_2229_76_1 : List RowType := [(11,17),(11,23),(11,29),(11,35),(16,26),(16,32),(16,38),(16,44),(21,27),(21,33),(21,39),(21,45)]
private def stage_0_frontier_mixed_2229_76_1 : Stage := [
  ((11,17),⟨⟨(-153846),0,0,0⟩,[0,0,0],1⟩),
  ((11,23),⟨⟨(-153846),0,0,0⟩,[0,0,0],1⟩),
  ((11,29),⟨⟨(-26),0,1,0⟩,[0,0,9],0⟩),
  ((11,35),⟨⟨(-26),0,1,0⟩,[0,0,9],0⟩),
  ((16,26),⟨⟨(-212016),0,0,0⟩,[0,0,0],1⟩),
  ((16,32),⟨⟨(-212016),0,0,0⟩,[0,0,0],1⟩),
  ((16,38),⟨⟨(-212016),0,0,0⟩,[0,0,0],1⟩),
  ((16,44),⟨⟨(-17),0,1,0⟩,[0,0,0],0⟩),
  ((21,27),⟨⟨(-153846),0,0,0⟩,[0,0,0],1⟩),
  ((21,33),⟨⟨(-25872),(-11634),0,0⟩,[7350,0,0],1⟩),
  ((21,39),⟨⟨14,(-9),5,0⟩,[40,0,0],0⟩),
  ((21,45),⟨⟨(-17),0,1,0⟩,[0,0,0],0⟩)]
private theorem frontier_mixed_2229_76_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2229) : ¬∃ f : G → ℤ, IsSDS 76 1 f :=
  abelian_short_mixed G 3 743 7 4 5 1 76 1 25 16 2 33 248 1
    types_frontier_mixed_2229_76_1 [stage_0_frontier_mixed_2229_76_1] ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2229_2209_2134 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2229) : ¬∃ f : G → ℤ, IsSDS 2209 2134 f :=
  abelian_short_linear G 3 743 7 3 5 1 2209 2134 25 727 2 33
    ⟨⟨722,(-1),0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2343_77_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2343) : ¬∃ f : G → ℤ, IsSDS 77 2 f :=
  abelian_short_linear G 3 781 7 1 5 1 77 2 25 23 2 33
    ⟨⟨(-2166),159,25,(-4)⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2343_2282_2207 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2343) : ¬∃ f : G → ℤ, IsSDS 2282 2207 f :=
  abelian_short_linear G 3 781 7 1 5 1 2282 2207 25 758 2 33
    ⟨⟨(-763),1,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2841_76_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2841) : ¬∃ f : G → ℤ, IsSDS 76 1 f :=
  abelian_short_linear G 3 947 7 3 5 1 76 1 25 18 2 33
    ⟨⟨(-76),(-3),5,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2841_2809_2734 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2841) : ¬∃ f : G → ℤ, IsSDS 2809 2734 f :=
  abelian_short_linear G 3 947 7 3 5 1 2809 2734 25 929 2 33
    ⟨⟨(-941),0,1,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4281_76_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4281) : ¬∃ f : G → ℤ, IsSDS 76 1 f :=
  abelian_short_linear G 3 1427 7 1 5 1 76 1 25 22 2 33
    ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4281_4225_4150 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4281) : ¬∃ f : G → ℤ, IsSDS 4225 4150 f :=
  abelian_short_linear G 3 1427 7 1 5 1 4225 4150 25 1405 2 33
    ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5109_76_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5109) : ¬∃ f : G → ℤ, IsSDS 76 1 f :=
  abelian_short_linear G 3 1703 7 0 5 1 76 1 25 24 2 33
    ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5109_5041_4966 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5109) : ¬∃ f : G → ℤ, IsSDS 5041 4966 f :=
  abelian_short_linear G 3 1703 7 0 5 1 5041 4966 25 1679 2 33
    ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_3_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=3*m)
    (hm : 3 < m) (hn : k-l=(3:ℤ)*25) : False := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_3_25
  simp only [keep_3_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=100 := by omega
    rw [hk,hL] at hf
    exact Long141.case_N4562 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=121 := by omega
    rw [hk,hL] at hf
    exact Long141.case_N4585 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=97 := by omega
    rw [hk,hL] at hf
    exact Long177.case_N7523 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=148 := by omega
    rw [hk,hL] at hf
    exact Long177.case_N7554 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=97 := by omega
    rw [hk,hL] at hf
    exact Long213.case_N11037 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=172 := by omega
    rw [hk,hL] at hf
    exact Long213.case_N11079 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=76 := by omega
    rw [hk,hL] at hf
    exact Long249.case_N15911 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=100 := by omega
    rw [hk,hL] at hf
    exact Long321.case_N27763 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=241 := by omega
    rw [hk,hL] at hf
    exact Long321.case_N27821 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=77 := by omega
    rw [hk,hL] at hf
    exact Long327.case_N29170 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=88 := by omega
    rw [hk,hL] at hf
    exact Long393.case_N43009 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=337 := by omega
    rw [hk,hL] at hf
    exact Long393.case_N43123 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=76 := by omega
    rw [hk,hL] at hf
    exact fibre_501_76 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=77 := by omega
    rw [hk,hL] at hf
    exact reduced_507_77 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=88 := by omega
    rw [hk,hL] at hf
    exact fibre_537_88 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=457 := by omega
    rw [hk,hL] at hf
    exact fibre_537_457 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=77 := by omega
    rw [hk,hL] at hf
    exact fibre_1263_77 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1238 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1263_1238_1163 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=77 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1587_77_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1550 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1587_1550_1475 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=76 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1689_76_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1681 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1689_1681_1606 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=77 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1947_77_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1898 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1947_1898_1823 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=76 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2229_76_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2209 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2229_2209_2134 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=77 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2343_77_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2282 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2343_2282_2207 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=76 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2841_76_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2809 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2841_2809_2734 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=76 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4281_76_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4281_4225_4150 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=76 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5109_76_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5041 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5109_5041_4966 G hg ⟨f,hf⟩

end Signed39.Contraction
