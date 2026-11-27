import Signed18ColdPrime7Part0
import Signed18ColdPrime7Part12
import Signed18ColdPrime7Part24
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification
import SignedFullConjugacy

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_7_18 : divisorGrid 7 18 93 qInputs_7_18 keep_7_18 := by
  intro d
  fin_cases d
  · exact slice18x7x0
  · exact slice18x7x1
  · exact slice18x7x2
  · exact slice18x7x3
  · exact slice18x7x4
  · exact slice18x7x5
  · exact slice18x7x6
  · exact slice18x7x7
  · exact slice18x7x8
  · exact slice18x7x9
  · exact slice18x7x10
  · exact slice18x7x11
  · exact slice18x7x12
  · exact slice18x7x13
  · exact slice18x7x14
  · exact slice18x7x15
  · exact slice18x7x16
  · exact slice18x7x17
  · exact slice18x7x18
  · exact slice18x7x19
  · exact slice18x7x20
  · exact slice18x7x21
  · exact slice18x7x22
  · exact slice18x7x23
  · exact slice18x7x24
  · exact slice18x7x25
  · exact slice18x7x26
  · exact slice18x7x27
  · exact slice18x7x28
  · exact slice18x7x29
  · exact slice18x7x30
  · exact slice18x7x31
  · exact slice18x7x32
  · exact slice18x7x33
  · exact slice18x7x34
  · exact slice18x7x35


private def types_frontier_mixed_329_128_2 : List RowType := [((-5),19),((-5),33),((-5),47),((-2),12),((-2),26),((-2),40),(1,17),(1,31),(1,45),(4,20),(4,34),(7,21),(7,35),(10,20),(10,34),(13,17),(13,31),(13,45)]
private def stage_0_frontier_mixed_329_128_2 : Stage := [
  (((-5),19),⟨⟨(-67114684),(-125194699),0,9913428⟩,[302016078,0,0,0,0,0,0],105921⟩),
  (((-5),33),⟨⟨(-140),(-14),9,1⟩,[0,0,0,0,0,0,0],0⟩),
  (((-5),47),⟨⟨(-140),(-14),9,1⟩,[0,0,0,0,0,0,0],0⟩),
  (((-2),12),⟨⟨(-28952),(-25991),0,2023⟩,[94752,0,0,0,0,0,0],27⟩),
  (((-2),26),⟨⟨(-5600),(-560),360,63⟩,[0,0,0,0,0,0,0],0⟩),
  (((-2),40),⟨⟨(-140),(-14),9,1⟩,[0,0,0,0,0,0,0],0⟩),
  ((1,31),⟨⟨(-5600),(-560),360,63⟩,[0,0,0,0,0,0,0],0⟩),
  ((1,45),⟨⟨(-140),(-14),9,1⟩,[0,0,0,0,0,0,0],0⟩),
  ((4,34),⟨⟨(-5600),(-560),360,63⟩,[0,0,0,0,0,0,0],0⟩),
  ((7,35),⟨⟨(-5600),(-560),360,63⟩,[0,0,0,0,0,0,0],0⟩),
  ((10,34),⟨⟨(-5600),(-560),360,63⟩,[0,0,0,0,0,0,0],0⟩),
  ((13,17),⟨⟨(-84224),(-23030),0,3304⟩,[0,0,0,0,76986,0,0],27⟩),
  ((13,31),⟨⟨(-5600),(-560),360,63⟩,[0,0,0,0,0,0,0],0⟩),
  ((13,45),⟨⟨0,(-58),3,7⟩,[0,0,0,0,60,0,0],0⟩)]
private theorem frontier_mixed_329_128_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=329) : ¬∃ f : G → ℤ, IsSDS 128 2 f :=
  abelian_short_mixed G 7 47 10 3 3 3 128 2 18 4 1 5 27 4
    types_frontier_mixed_329_128_2 [stage_0_frontier_mixed_329_128_2] ⟨⟨(-20),0,1,0⟩,[0,3,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6209_128_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6209) : ¬∃ f : G → ℤ, IsSDS 128 2 f :=
  abelian_short_linear G 7 887 10 1 3 3 128 2 18 16 1 5
    ⟨⟨0,(-616),75,13⟩,[0,210,378,210,0,336,336],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6209_6113_5987 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6209) : ¬∃ f : G → ℤ, IsSDS 6113 5987 f :=
  abelian_short_linear G 7 887 10 1 3 3 6113 5987 18 871 1 5
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_7_18_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=7*m)
    (hm : 7 < m) (hn : k-l=(7:ℤ)*18) : False := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have row := endpoint_case (s:=18) hf hg hn (by decide) hm grid_7_18
  simp only [keep_7_18,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=148 := by omega
    rw [hk,hL] at hf
    exact full_217_148_22 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=128 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_329_128_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=128 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6209_128_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6113 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6209_6113_5987 G hg ⟨f,hf⟩

end Signed39.Contraction
