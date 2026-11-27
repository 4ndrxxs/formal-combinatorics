import Signed20ColdPrime31Part0
import Signed20ColdPrime31Part12
import Signed20ColdPrime31Part24
import Signed20ColdPrime31Part36
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_31_20 : divisorGrid 31 20 218 qInputs_31_20 keep_31_20 := by
  intro d
  fin_cases d
  · exact slice20x31x0
  · exact slice20x31x1
  · exact slice20x31x2
  · exact slice20x31x3
  · exact slice20x31x4
  · exact slice20x31x5
  · exact slice20x31x6
  · exact slice20x31x7
  · exact slice20x31x8
  · exact slice20x31x9
  · exact slice20x31x10
  · exact slice20x31x11
  · exact slice20x31x12
  · exact slice20x31x13
  · exact slice20x31x14
  · exact slice20x31x15
  · exact slice20x31x16
  · exact slice20x31x17
  · exact slice20x31x18
  · exact slice20x31x19
  · exact slice20x31x20
  · exact slice20x31x21
  · exact slice20x31x22
  · exact slice20x31x23
  · exact slice20x31x24
  · exact slice20x31x25
  · exact slice20x31x26
  · exact slice20x31x27
  · exact slice20x31x28
  · exact slice20x31x29
  · exact slice20x31x30
  · exact slice20x31x31
  · exact slice20x31x32
  · exact slice20x31x33
  · exact slice20x31x34
  · exact slice20x31x35
  · exact slice20x31x36
  · exact slice20x31x37
  · exact slice20x31x38
  · exact slice20x31x39


private theorem frontier_mixed_1705_676_56 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1705) : ¬∃ f : G → ℤ, IsSDS 676 56 f :=
  abelian_short_linear G 31 55 24 1 1 0 676 56 20 10 7 9
    ⟨⟨0,(-2666),247,115⟩,[0,0,0,0,0,0,0,0,3100,0,0,0,0,0,6386,0,372,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2449_865_245 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2449) : ¬∃ f : G → ℤ, IsSDS 865 245 f :=
  abelian_short_linear G 31 79 24 1 1 0 865 245 20 25 7 9
    ⟨⟨0,(-49011),14651,628⟩,[0,0,0,0,0,100750,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18538,0,26970,0,0,0,0,289788],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2449_1764_1144 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2449) : ¬∃ f : G → ℤ, IsSDS 1764 1144 f :=
  abelian_short_linear G 31 79 24 0 1 0 1764 1144 20 54 7 9
    ⟨⟨0,0,2025,(-79)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,66154,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3131_664_44 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3131) : ¬∃ f : G → ℤ, IsSDS 664 44 f :=
  abelian_short_linear G 31 101 24 1 1 0 664 44 20 12 7 9
    ⟨⟨0,(-1395),182,47⟩,[0,0,0,0,0,0,0,0,0,558,0,0,0,0,3038,0,0,0,0,620,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3131_3051_2431 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3131) : ¬∃ f : G → ℤ, IsSDS 3051 2431 f :=
  abelian_short_linear G 31 101 24 0 1 0 3051 2431 20 89 7 9
    ⟨⟨(-101),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4681_625_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4681) : ¬∃ f : G → ℤ, IsSDS 625 5 f :=
  abelian_short_linear G 31 151 24 2 1 0 625 5 20 5 7 9
    ⟨⟨(-253022),(-2697),4845,134⟩,[253022,0,0,0,0,0,0,0,43152,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5549_676_56 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5549) : ¬∃ f : G → ℤ, IsSDS 676 56 f :=
  abelian_short_linear G 31 179 24 1 1 0 676 56 20 18 7 9
    ⟨⟨0,(-8339),1218,205⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3348,10602,0,14136,10416,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5549_5109_4489 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5549) : ¬∃ f : G → ℤ, IsSDS 5109 4489 f :=
  abelian_short_linear G 31 179 24 0 1 0 5109 4489 20 161 7 9
    ⟨⟨(-179),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_15221_624_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=15221) : ¬∃ f : G → ℤ, IsSDS 624 4 f :=
  abelian_short_linear G 31 491 24 6 1 0 624 4 20 8 7 9
    ⟨⟨(-42),(-5),1,0⟩,[42,10,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_19189_640_20 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=19189) : ¬∃ f : G → ℤ, IsSDS 640 20 f :=
  abelian_short_linear G 31 619 24 0 1 0 640 20 20 20 7 9
    ⟨⟨0,(-31),1,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_19189_18589_17969 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=19189) : ¬∃ f : G → ℤ, IsSDS 18589 17969 f :=
  abelian_short_linear G 31 619 24 0 1 0 18589 17969 20 599 7 9
    ⟨⟨(-619),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23405_621_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23405) : ¬∃ f : G → ℤ, IsSDS 621 1 f :=
  abelian_short_linear G 31 755 24 7 1 0 621 1 20 5 7 9
    ⟨⟨(-36864740),0,756860,0⟩,[36864740,0,0,0,0,0,680251,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,680251,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_34441_624_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=34441) : ¬∃ f : G → ℤ, IsSDS 624 4 f :=
  abelian_short_linear G 31 1111 24 4 1 0 624 4 20 12 7 9
    ⟨⟨(-4626),(-1215),92,7⟩,[4626,2430,0,388,542,0,0,0,1386,0,804,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_34441_34321_33701 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=34441) : ¬∃ f : G → ℤ, IsSDS 34321 33701 f :=
  abelian_short_linear G 31 1111 24 0 1 0 34321 33701 20 1099 7 9
    ⟨⟨(-1111),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_46469_621_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=46469) : ¬∃ f : G → ℤ, IsSDS 621 1 f :=
  abelian_short_linear G 31 1499 24 6 1 0 621 1 20 7 7 9
    ⟨⟨(-93930),(-5177),1365,(-172)⟩,[93930,0,12152,0,0,51770,0,17112,15314,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_61349_624_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=61349) : ¬∃ f : G → ℤ, IsSDS 624 4 f :=
  abelian_short_linear G 31 1979 24 2 1 0 624 4 20 16 7 9
    ⟨⟨(-14364),(-4906),255,23⟩,[14364,9812,2154,7200,9140,7974,3702,0,1650,3870,2984,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_61349_60981_60361 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=61349) : ¬∃ f : G → ℤ, IsSDS 60981 60361 f :=
  abelian_short_linear G 31 1979 24 0 1 0 60981 60361 20 1963 7 9
    ⟨⟨(-1979),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_95945_624_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=95945) : ¬∃ f : G → ℤ, IsSDS 624 4 f :=
  abelian_short_linear G 31 3095 24 0 1 0 624 4 20 20 7 9
    ⟨⟨0,(-2500),129,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_95945_95329_94709 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=95945) : ¬∃ f : G → ℤ, IsSDS 95329 94709 f :=
  abelian_short_linear G 31 3095 24 0 1 0 95329 94709 20 3075 7 9
    ⟨⟨(-3095),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_346301_621_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=346301) : ¬∃ f : G → ℤ, IsSDS 621 1 f :=
  abelian_short_linear G 31 11171 24 0 1 0 621 1 20 19 7 9
    ⟨⟨0,(-28305000),1514817,0⟩,[0,0,0,0,0,0,0,0,0,3639200,0,1514817,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_346301_345744_345124 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=346301) : ¬∃ f : G → ℤ, IsSDS 345744 345124 f :=
  abelian_short_linear G 31 11171 24 0 1 0 345744 345124 20 11152 7 9
    ⟨⟨(-11171),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_31_20_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=31*m)
    (hm : 31 < m) (hn : k-l=(31:ℤ)*20) : False := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  have row := endpoint_case (s:=20) hf hg hn (by decide) hm grid_31_20
  simp only [keep_31_20,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=676 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1705_676_56 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=865 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2449_865_245 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1764 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2449_1764_1144 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=664 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3131_664_44 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3051 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3131_3051_2431 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4681_625_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=676 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5549_676_56 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5109 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5549_5109_4489 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=624 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_15221_624_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=640 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_19189_640_20 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=18589 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_19189_18589_17969 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=621 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23405_621_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=624 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_34441_624_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=34321 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_34441_34321_33701 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=621 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_46469_621_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=624 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_61349_624_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=60981 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_61349_60981_60361 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=624 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_95945_624_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=95329 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_95945_95329_94709 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=621 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_346301_621_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=345744 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_346301_345744_345124 G hg ⟨f,hf⟩

end Signed39.Contraction
