import Signed28Grid31Part0
import Signed28Grid31Part12
import Signed28Grid31Part24
import Signed28Grid31Part36
import Signed28Grid31Part48
import Signed249Reduced
import Signed249Reduced
import SignedReducedPrimeCases
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_31_28 : divisorGrid 31 28 307 qInputs_31_28 keep_31_28 := by
  intro d
  fin_cases d
  · exact grid31x28Case0
  · exact grid31x28Case1
  · exact grid31x28Case2
  · exact grid31x28Case3
  · exact grid31x28Case4
  · exact grid31x28Case5
  · exact grid31x28Case6
  · exact grid31x28Case7
  · exact grid31x28Case8
  · exact grid31x28Case9
  · exact grid31x28Case10
  · exact grid31x28Case11
  · exact grid31x28Case12
  · exact grid31x28Case13
  · exact grid31x28Case14
  · exact grid31x28Case15
  · exact grid31x28Case16
  · exact grid31x28Case17
  · exact grid31x28Case18
  · exact grid31x28Case19
  · exact grid31x28Case20
  · exact grid31x28Case21
  · exact grid31x28Case22
  · exact grid31x28Case23
  · exact grid31x28Case24
  · exact grid31x28Case25
  · exact grid31x28Case26
  · exact grid31x28Case27
  · exact grid31x28Case28
  · exact grid31x28Case29
  · exact grid31x28Case30
  · exact grid31x28Case31
  · exact grid31x28Case32
  · exact grid31x28Case33
  · exact grid31x28Case34
  · exact grid31x28Case35
  · exact grid31x28Case36
  · exact grid31x28Case37
  · exact grid31x28Case38
  · exact grid31x28Case39
  · exact grid31x28Case40
  · exact grid31x28Case41
  · exact grid31x28Case42
  · exact grid31x28Case43
  · exact grid31x28Case44
  · exact grid31x28Case45
  · exact grid31x28Case46
  · exact grid31x28Case47
  · exact grid31x28Case48
  · exact grid31x28Case49
  · exact grid31x28Case50
  · exact grid31x28Case51
  · exact grid31x28Case52
  · exact grid31x28Case53
  · exact grid31x28Case54
  · exact grid31x28Case55



private theorem frontier_mixed_2511_1480_612 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2511) : ¬∃ f : G → ℤ, IsSDS 1480 612 f :=
  abelian_short_linear G 31 81 28 1 1 0 1480 612 28 40 5 9
    ⟨⟨(-62992),0,1280,(-7)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16399,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2511_1511_643 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2511) : ¬∃ f : G → ℤ, IsSDS 1511 643 f :=
  abelian_short_linear G 31 81 28 1 1 0 1511 643 28 41 5 9
    ⟨⟨(-2480),0,81,(-1)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_2573_877_9 : List RowType := [((-23),37),((-18),42),((-17),61),((-15),55),((-13),73),((-12),60),((-11),53),((-10),52),((-9),57),((-8),68),((-6),46),((-5),75),((-4),48),((-2),74),((-1),65),(0,0),(0,62),(1,65),(2,74),(4,48),(5,75),(6,46),(8,68),(9,57),(10,52),(11,53),(12,60),(13,73),(15,55),(17,61),(18,42),(23,37),(24,54),(25,77),(26,44),(27,79),(28,58)]
private def stage_0_frontier_mixed_2573_877_9 : Stage := [
  (((-12),60),⟨⟨0,(-295895),0,18755⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],91⟩),
  (((-11),53),⟨⟨(-30876),(-223851),0,12927⟩,[30876,0,0,0,0,0,0,0,0,0,0,0,0,30876,0,108066,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],20⟩),
  (((-10),52),⟨⟨(-138942),(-33449),0,1333⟩,[138942,66898,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],14⟩),
  (((-6),46),⟨⟨0,(-445129),0,31217⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],70⟩),
  (((-4),48),⟨⟨(-2346576),(-5146),26145,3281⟩,[2346576,0,0,0,0,0,0,0,20584,0,102920,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],23⟩),
  (((-2),74),⟨⟨(-3756580),0,39093,2629⟩,[3756580,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],102⟩),
  ((2,74),⟨⟨(-3756580),0,39093,2629⟩,[3756580,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],102⟩),
  ((4,48),⟨⟨(-2346576),(-5146),26145,3281⟩,[2346576,0,0,0,0,0,0,0,20584,0,102920,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],23⟩),
  ((6,46),⟨⟨(-45032646),(-666407),0,67363⟩,[45032646,0,0,0,0,0,0,0,0,0,0,0,15993768,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],2261⟩),
  ((8,68),⟨⟨0,(-280457),23406,10661⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],27⟩),
  ((10,52),⟨⟨(-138942),(-33449),0,1333⟩,[138942,66898,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],14⟩),
  ((11,53),⟨⟨(-241862),(-56606),0,3906⟩,[241862,113212,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],15⟩),
  ((12,60),⟨⟨(-1775370),0,0,4650⟩,[1775370,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],133⟩),
  ((13,73),⟨⟨0,(-190402),12118,10611⟩,[0,0,0,0,0,0,0,0,0,0,0,23157,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((15,55),⟨⟨(-3658806),(-288176),86403,15823⟩,[3658806,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],18⟩),
  ((18,42),⟨⟨0,(-439983),0,26877⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],110⟩),
  ((24,54),⟨⟨(-3190520),(-97774),0,22041⟩,[3190520,0,0,0,0,0,1173288,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],80⟩),
  ((25,77),⟨⟨0,(-23436),530,1138⟩,[0,0,0,0,0,0,0,0,0,0,0,0,3100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],5⟩),
  ((26,44),⟨⟨(-432264),(-66898),0,(-1643)⟩,[432264,0,267592,0,123504,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],120⟩),
  ((28,58),⟨⟨(-499162),0,0,4712⟩,[499162,0,0,0,41168,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41168,0,0,0],11⟩)]
private theorem frontier_mixed_2573_877_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2573) : ¬∃ f : G → ℤ, IsSDS 877 9 f :=
  abelian_short_mixed G 31 83 28 1 1 0 877 9 28 5 5 9 75 28
    types_frontier_mixed_2573_877_9 [stage_0_frontier_mixed_2573_877_9] ⟨⟨(-62880927),(-273544),970641,62871⟩,[62880927,0,0,0,0,0,0,0,0,4923792,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4309_1141_273 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4309) : ¬∃ f : G → ℤ, IsSDS 1141 273 f :=
  abelian_short_linear G 31 139 28 0 1 0 1141 273 28 35 5 9
    ⟨⟨(-442),(-229),70,3⟩,[0,498,0,0,512,0,0,0,0,0,0,8,1032,0,120,0,118,0,0,0,0,0,0,0,0,0,0,168,0,0,412],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4309_3280_2412 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4309) : ¬∃ f : G → ℤ, IsSDS 3280 2412 f :=
  abelian_short_linear G 31 139 28 0 1 0 3280 2412 28 104 5 9
    ⟨⟨0,0,4418,(-61)⟩,[0,0,0,0,30535,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,25792,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_215357_869_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=215357) : ¬∃ f : G → ℤ, IsSDS 869 1 f :=
  abelian_short_linear G 31 6947 28 6 1 0 869 1 28 15 5 9
    ⟨⟨0,(-8649),364,137⟩,[0,0,0,1054,372,6696,0,0,0,11780,7998,11222,0,0,0,3906,0,0,4278,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_215357_215296_214428 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=215357) : ¬∃ f : G → ℤ, IsSDS 215296 214428 f :=
  abelian_short_linear G 31 6947 28 0 1 0 215296 214428 28 6932 5 9
    ⟨⟨(-6947),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_699701_869_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=699701) : ¬∃ f : G → ℤ, IsSDS 869 1 f :=
  abelian_short_linear G 31 22571 28 0 1 0 869 1 28 27 5 9
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_699701_698896_698028 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=699701) : ¬∃ f : G → ℤ, IsSDS 698896 698028 f :=
  abelian_short_linear G 31 22571 28 0 1 0 698896 698028 28 22544 5 9
    ⟨⟨(-22571),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_31_28_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=31*m)
    (hm : 31 < m) (hn : k-l=(31:ℤ)*28) : False := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  have row := endpoint_case (s:=28) hf hg hn (by decide) hm grid_31_28
  simp only [keep_31_28,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1480 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2511_1480_612 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1511 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2511_1511_643 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=877 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2573_877_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1141 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4309_1141_273 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3280 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4309_3280_2412 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=871 := by omega
    rw [hk,hL] at hf
    exact reduced_7719_871 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=869 := by omega
    rw [hk,hL] at hf
    exact reduced_7781_869 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=869 := by omega
    rw [hk,hL] at hf
    exact reduced_23157_869 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=869 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_215357_869_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=215296 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_215357_215296_214428 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=869 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_699701_869_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=698896 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_699701_698896_698028 G hg ⟨f,hf⟩

end Signed39.Contraction
