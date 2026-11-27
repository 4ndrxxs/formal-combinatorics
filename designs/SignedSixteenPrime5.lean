import SignedBinaryFibreCases
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_5_16 : ℕ → Option QuotientInput
  | 29 => some ⟨29,5,7,0,16⟩
  | 41 => some ⟨41,5,10,0,16⟩
  | 61 => some ⟨61,5,15,0,16⟩
  | 229 => some ⟨229,5,57,0,16⟩
  | 241 => some ⟨241,5,20,0,16⟩
  | 1109 => some ⟨1109,5,277,0,16⟩
  | _ => none

private def keep_5_16 : List (ℕ × ℤ) := [(31,19),(31,64),(59,71),(59,76),(79,16),(79,251),(109,1),(121,4),(121,509),(389,1),(389,1856),(589,1),(589,2836),(829,1),(829,4016)]

private theorem grid_5_16 : divisorGrid 5 16 70 qInputs_5_16 keep_5_16 := by decide +kernel

private theorem frontier_mixed_155_144_64 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=155) : ¬∃ f : G → ℤ, IsSDS 144 64 f :=
  abelian_short_linear G 5 31 8 1 2 2 144 64 16 20 3 19
    ⟨⟨3940,0,(-144),(-1)⟩,[780,60,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_295_151_71 : List RowType := [(25,25),(27,31),(29,29),(35,35),(37,41)]
private def stage_0_frontier_mixed_295_151_71 : Stage := [
  ((25,25),⟨⟨(-8757),(-111),264,0⟩,[3112,0,0,0,0],1⟩),
  ((35,35),⟨⟨17346,(-1947),531,18⟩,[5664,0,0,0,0],2⟩),
  ((37,41),⟨⟨675,(-52),0,1⟩,[0,0,0,0,0],0⟩)]
private theorem frontier_mixed_295_151_71 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=295) : ¬∃ f : G → ℤ, IsSDS 151 71 f :=
  abelian_short_mixed G 5 59 8 0 2 2 151 71 16 29 3 19 12 1
    types_frontier_mixed_295_151_71 [stage_0_frontier_mixed_295_151_71] ⟨⟨58,(-1),(-1),0⟩,[0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_295_156_76 : List RowType := [(22,26),(24,24),(30,30),(32,36),(34,34)]
private def stage_0_frontier_mixed_295_156_76 : Stage := [
  ((22,26),⟨⟨1088,(-66),0,1⟩,[0,0,0,0,0],0⟩),
  ((24,24),⟨⟨(-16500),(-339),603,0⟩,[0,0,0,0,6384],2⟩),
  ((34,34),⟨⟨5310,(-767),236,7⟩,[0,0,0,0,2832],1⟩)]
private theorem frontier_mixed_295_156_76 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=295) : ¬∃ f : G → ℤ, IsSDS 156 76 f :=
  abelian_short_mixed G 5 59 8 0 2 2 156 76 16 30 3 19 12 1
    types_frontier_mixed_295_156_76 [stage_0_frontier_mixed_295_156_76] ⟨⟨(-60),3,(-1),0⟩,[0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_395_96_16 : List RowType := [(8,16),(10,10),(10,20),(12,16),(12,26),(14,24),(16,24),(18,26),(20,20),(20,30),(22,26),(22,36),(24,24),(24,34)]
private def stage_0_frontier_mixed_395_96_16 : Stage := [
  ((8,16),⟨⟨667065000,(-158825000),33353250,3850000⟩,[0,0,0,0,0],44471⟩),
  ((10,10),⟨⟨0,0,0,(-110000)⟩,[0,0,0,0,0],9307⟩),
  ((10,20),⟨⟨(-2013447024),0,0,(-1991124)⟩,[0,0,0,0,0],424793⟩),
  ((12,16),⟨⟨(-1230030),0,56643,(-2142)⟩,[0,0,61620,0,188020],133⟩),
  ((12,26),⟨⟨0,(-136670),57512,2437⟩,[72680,0,60040,0,0],72⟩),
  ((14,24),⟨⟨417120,(-116525),27255,2985⟩,[148520,0,112180,0,0],4⟩),
  ((18,26),⟨⟨144,(-40),10,1⟩,[56,0,32,0,0],0⟩),
  ((20,20),⟨⟨(-15360),20,480,0⟩,[4970,0,0,0,0],1⟩),
  ((20,30),⟨⟨144,(-40),10,1⟩,[56,0,32,0,0],0⟩),
  ((22,26),⟨⟨0,(-5530),0,245⟩,[0,0,0,0,0],4⟩),
  ((22,36),⟨⟨144,(-40),10,1⟩,[56,0,32,0,0],0⟩),
  ((24,24),⟨⟨832160000,(-300915000),37893000,9583750⟩,[0,0,14860000,0,423510000],138941⟩),
  ((24,34),⟨⟨0,(-23511901),9011530,528352⟩,[45876880,0,19006136,0,0],6222⟩)]
private theorem frontier_mixed_395_96_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=395) : ¬∃ f : G → ℤ, IsSDS 96 16 f :=
  abelian_short_mixed G 5 79 8 1 2 2 96 16 16 16 3 19 16 1
    types_frontier_mixed_395_96_16 [stage_0_frontier_mixed_395_96_16] ⟨⟨(-24),0,1,0⟩,[0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_395_331_251 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=395) : ¬∃ f : G → ℤ, IsSDS 331 251 f :=
  abelian_short_linear G 5 79 8 1 2 2 331 251 16 63 3 19
    ⟨⟨4071,(-130),2,1⟩,[0,0,8,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_545_81_1 : List RowType := [((-3),11),((-3),21),((-3),31),((-3),41),((-3),51),((-1),9),((-1),19),((-1),29),((-1),39),((-1),49),(1,9),(1,19),(1,29),(1,39),(1,49),(3,11),(3,21),(3,31),(3,41),(3,51),(5,15),(5,25),(5,35),(5,45),(5,55),(7,11),(7,21),(7,31),(7,41),(7,51),(7,61),(9,19),(9,29),(9,39),(9,49),(9,59),(11,19),(11,29),(11,39),(11,49),(11,59),(13,21),(13,31),(13,41),(13,51),(13,61)]
private def stage_0_frontier_mixed_545_81_1 : Stage := [
  (((-3),11),⟨⟨0,(-84475),0,5575⟩,[249610,0,91560,16350,0],21⟩),
  (((-3),21),⟨⟨27,(-12),0,1⟩,[8,0,8,0,0],0⟩),
  (((-3),31),⟨⟨27,(-12),0,1⟩,[8,0,8,0,0],0⟩),
  (((-3),41),⟨⟨27,(-12),0,1⟩,[8,0,8,0,0],0⟩),
  (((-3),51),⟨⟨27,(-12),0,1⟩,[8,0,8,0,0],0⟩),
  (((-1),9),⟨⟨(-425315000),0,0,371875⟩,[392040000,0,0,0,0],57596⟩),
  (((-1),29),⟨⟨(-564075),(-91560),64092,2247⟩,[0,0,274680,0,0],8⟩),
  (((-1),39),⟨⟨(-196745),(-11445),17440,(-370)⟩,[0,22890,59950,0,0],3⟩),
  (((-1),49),⟨⟨(-1478585),0,109000,(-6775)⟩,[0,274680,265960,0,274680],24⟩),
  ((1,9),⟨⟨(-425315000),0,0,371875⟩,[392040000,0,0,0,0],57596⟩),
  ((1,39),⟨⟨(-196745),(-11445),17440,(-370)⟩,[0,22890,59950,0,0],3⟩),
  ((1,49),⟨⟨(-1478585),0,109000,(-6775)⟩,[0,274680,265960,0,274680],24⟩),
  ((3,11),⟨⟨(-50218850),(-1611300),0,170000⟩,[46190600,0,0,9667800,0],5371⟩),
  ((3,41),⟨⟨(-93),4,10,(-1)⟩,[0,0,4,0,8],0⟩),
  ((3,51),⟨⟨(-93),4,10,(-1)⟩,[0,0,4,0,8],0⟩),
  ((5,45),⟨⟨(-135),4,12,(-1)⟩,[0,24,24,0,32],0⟩),
  ((5,55),⟨⟨(-135),4,12,(-1)⟩,[0,24,24,0,32],0⟩),
  ((7,11),⟨⟨(-115431),0,0,231⟩,[81096,0,57552,27032,0],8⟩),
  ((7,41),⟨⟨(-10),(-1),1,0⟩,[0,2,6,2,0],0⟩),
  ((7,51),⟨⟨(-10),(-1),1,0⟩,[0,2,6,2,0],0⟩),
  ((7,61),⟨⟨(-10),(-1),1,0⟩,[0,2,6,2,0],0⟩),
  ((9,19),⟨⟨(-35861),0,0,261⟩,[11336,0,0,0,0],4⟩),
  ((9,49),⟨⟨(-970645),0,96792,(-7283)⟩,[0,0,117720,0,0],12⟩),
  ((9,59),⟨⟨(-970645),0,96792,(-7283)⟩,[0,0,117720,0,0],12⟩),
  ((11,19),⟨⟨(-563491875),0,0,6235000⟩,[113145000,0,0,0,0],69078⟩),
  ((11,49),⟨⟨(-95),(-20),8,3⟩,[0,40,0,40,0],0⟩),
  ((11,59),⟨⟨(-12179193),(-553420),1305080,0⟩,[0,1111530,4075610,0,0],0⟩),
  ((13,21),⟨⟨(-5),(-4),0,1⟩,[0,8,0,8,0],0⟩),
  ((13,31),⟨⟨(-5),(-4),0,1⟩,[0,8,0,8,0],0⟩),
  ((13,41),⟨⟨(-5),(-4),0,1⟩,[0,8,0,8,0],0⟩),
  ((13,51),⟨⟨(-5),(-4),0,1⟩,[0,8,0,8,0],0⟩),
  ((13,61),⟨⟨(-5),(-4),0,1⟩,[0,8,0,8,0],0⟩)]
private theorem frontier_mixed_545_81_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=545) : ¬∃ f : G → ℤ, IsSDS 81 1 f :=
  abelian_short_mixed G 5 109 8 5 2 2 81 1 16 5 3 19 22 1
    types_frontier_mixed_545_81_1 [stage_0_frontier_mixed_545_81_1] ⟨⟨(-227),0,12,(-1)⟩,[72,0,24,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_605_84_4 : List RowType := [(2,14),(2,24),(2,34),(4,16),(4,26),(4,36),(6,16),(6,26),(6,36),(8,14),(8,24),(8,34),(10,10),(10,20),(10,30),(10,40),(12,14),(12,24),(12,34),(12,44),(14,16),(14,26),(14,36),(14,46),(16,16),(16,26),(16,36),(16,46),(18,24),(18,34),(18,44)]
private def stage_0_frontier_mixed_605_84_4 : Stage := [
  ((2,14),⟨⟨(-156332),0,0,83⟩,[117612,0,0,14520,0],13⟩),
  ((2,24),⟨⟨198440000,(-45677500),0,1788750⟩,[67760000,0,25410000,0,0],6413⟩),
  ((2,34),⟨⟨0,(-13115),5124,520⟩,[28060,0,10980,0,0],0⟩),
  ((4,16),⟨⟨(-231110),0,0,90⟩,[163350,54450,0,9680,122210],13⟩),
  ((4,36),⟨⟨(-416),14,28,(-1)⟩,[96,0,0,0,0],0⟩),
  ((6,16),⟨⟨(-121242),0,0,123⟩,[63162,69454,0,0,25894],7⟩),
  ((6,36),⟨⟨(-416),14,28,(-1)⟩,[96,0,0,0,0],0⟩),
  ((8,14),⟨⟨(-48400000),0,0,190000⟩,[0,0,10890000,0,0],3993⟩),
  ((10,10),⟨⟨0,0,0,(-330000)⟩,[0,0,0,0,0],9959⟩),
  ((10,20),⟨⟨0,(-121000),0,2000⟩,[0,0,0,0,0],121⟩),
  ((10,40),⟨⟨(-608),14,40,(-1)⟩,[168,0,24,0,0],0⟩),
  ((12,14),⟨⟨(-1696420),0,0,3895⟩,[0,0,0,1081740,0],126⟩),
  ((12,44),⟨⟨(-320),0,24,0⟩,[105,0,20,0,0],0⟩),
  ((14,16),⟨⟨(-2665867500),0,0,6266000⟩,[138592500,46197500,0,461975000,1540822500],261967⟩),
  ((14,26),⟨⟨0,(-22506),0,1209⟩,[0,0,0,3872,14520],8⟩),
  ((14,46),⟨⟨(-304),7,20,0⟩,[84,0,12,0,0],0⟩),
  ((16,16),⟨⟨(-4848435000),0,0,22616000⟩,[0,3202545000,0,0,29745000],509631⟩),
  ((16,26),⟨⟨14585340,(-24135265),0,1777248⟩,[0,56257740,0,4861780,0],3444⟩),
  ((16,36),⟨⟨(-1090485600),(-27433600),70984440,2630000⟩,[270906800,0,0,0,0],8573⟩),
  ((16,46),⟨⟨(-16),0,1,0⟩,[6,0,2,2,0],0⟩),
  ((18,24),⟨⟨0,(-20570),0,1445⟩,[0,0,0,0,0],4⟩),
  ((18,34),⟨⟨0,(-20570),0,1445⟩,[0,0,0,0,0],4⟩),
  ((18,44),⟨⟨0,(-20570),0,1445⟩,[0,0,0,0,0],4⟩)]
private theorem frontier_mixed_605_84_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=605) : ¬∃ f : G → ℤ, IsSDS 84 4 f :=
  abelian_short_mixed G 5 121 8 3 2 2 84 4 16 10 3 19 97 4
    types_frontier_mixed_605_84_4 [stage_0_frontier_mixed_605_84_4] ⟨⟨(-95),0,4,0⟩,[0,0,35,15,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_605_589_509 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=605) : ¬∃ f : G → ℤ, IsSDS 589 509 f :=
  abelian_short_linear G 5 121 8 1 2 2 589 509 16 111 3 19
    ⟨⟨333,(-2),(-1),0⟩,[0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1945_81_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1945) : ¬∃ f : G → ℤ, IsSDS 81 1 f :=
  abelian_short_linear G 5 389 8 3 2 2 81 1 16 9 3 19
    ⟨⟨(-105),(-40),16,1⟩,[40,0,0,40,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1945_1936_1856 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1945) : ¬∃ f : G → ℤ, IsSDS 1936 1856 f :=
  abelian_short_linear G 5 389 8 1 2 2 1936 1856 16 380 3 19
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2945_81_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2945) : ¬∃ f : G → ℤ, IsSDS 81 1 f :=
  abelian_short_linear G 5 589 8 2 2 2 81 1 16 11 3 19
    ⟨⟨(-32),(-15),7,0⟩,[0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2945_2916_2836 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2945) : ¬∃ f : G → ℤ, IsSDS 2916 2836 f :=
  abelian_short_linear G 5 589 8 1 2 2 2916 2836 16 578 3 19
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4145_81_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4145) : ¬∃ f : G → ℤ, IsSDS 81 1 f :=
  abelian_short_linear G 5 829 8 1 2 2 81 1 16 13 3 19
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4145_4096_4016 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4145) : ¬∃ f : G → ℤ, IsSDS 4096 4016 f :=
  abelian_short_linear G 5 829 8 1 2 2 4096 4016 16 816 3 19
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_5_16_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=5*m)
    (hm : 5 < m) (hn : k-l=(5:ℤ)*16) : False := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have row := endpoint_case (s:=16) hf hg hn (by decide) hm grid_5_16
  simp only [keep_5_16,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=99 := by omega
    rw [hk,hL] at hf
    exact binary_155_99_19 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=144 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_155_144_64 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=151 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_295_151_71 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=156 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_295_156_76 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=96 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_395_96_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=331 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_395_331_251 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=81 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_545_81_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=84 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_605_84_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=589 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_605_589_509 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=81 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1945_81_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1936 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1945_1936_1856 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=81 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2945_81_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2916 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2945_2916_2836 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=81 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4145_81_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4096 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4145_4096_4016 G hg ⟨f,hf⟩

end Signed39.Contraction
