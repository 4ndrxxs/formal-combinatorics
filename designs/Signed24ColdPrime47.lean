import Signed24ColdPrime47Part0
import Signed24ColdPrime47Part12
import Signed24ColdPrime47Part24
import Signed24ColdPrime47Part36
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_47_24 : divisorGrid 47 24 323 qInputs_47_24 keep_47_24 := by
  intro d
  fin_cases d
  · exact slice24x47x0
  · exact slice24x47x1
  · exact slice24x47x2
  · exact slice24x47x3
  · exact slice24x47x4
  · exact slice24x47x5
  · exact slice24x47x6
  · exact slice24x47x7
  · exact slice24x47x8
  · exact slice24x47x9
  · exact slice24x47x10
  · exact slice24x47x11
  · exact slice24x47x12
  · exact slice24x47x13
  · exact slice24x47x14
  · exact slice24x47x15
  · exact slice24x47x16
  · exact slice24x47x17
  · exact slice24x47x18
  · exact slice24x47x19
  · exact slice24x47x20
  · exact slice24x47x21
  · exact slice24x47x22
  · exact slice24x47x23
  · exact slice24x47x24
  · exact slice24x47x25
  · exact slice24x47x26
  · exact slice24x47x27
  · exact slice24x47x28
  · exact slice24x47x29
  · exact slice24x47x30
  · exact slice24x47x31
  · exact slice24x47x32
  · exact slice24x47x33
  · exact slice24x47x34
  · exact slice24x47x35
  · exact slice24x47x36
  · exact slice24x47x37
  · exact slice24x47x38
  · exact slice24x47x39
  · exact slice24x47x40
  · exact slice24x47x41
  · exact slice24x47x42
  · exact slice24x47x43
  · exact slice24x47x44
  · exact slice24x47x45
  · exact slice24x47x46
  · exact slice24x47x47


private theorem frontier_mixed_7849_1156_28 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7849) : ¬∃ f : G → ℤ, IsSDS 1156 28 f :=
  abelian_short_linear G 47 167 33 2 1 0 1156 28 24 10 1 1
    ⟨⟨0,(-5405),546,167⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5264,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28153_1177_49 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28153) : ¬∃ f : G → ℤ, IsSDS 1177 49 f :=
  abelian_short_linear G 47 599 33 0 1 0 1177 49 24 25 1 1
    ⟨⟨0,(-3243),529,48⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6110,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28153_26980_25852 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28153) : ¬∃ f : G → ℤ, IsSDS 26980 25852 f :=
  abelian_short_linear G 47 599 33 0 1 0 26980 25852 24 574 1 1
    ⟨⟨(-599),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_54097_1129_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=54097) : ¬∃ f : G → ℤ, IsSDS 1129 1 f :=
  abelian_short_linear G 47 1151 33 9 1 0 1129 1 24 5 1 1
    ⟨⟨0,(-893),40,33⟩,[0,0,0,0,564,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_372193_1129_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=372193) : ¬∃ f : G → ℤ, IsSDS 1129 1 f :=
  abelian_short_linear G 47 7919 33 5 1 0 1129 1 24 13 1 1
    ⟨⟨0,(-1251690000),37235881,37235881⟩,[0,0,0,0,0,0,0,0,392680000,883530000,1472550000,2159740000,0,638105000,1619805000,0,687190000,0,147255000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_372193_372100_370972 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=372193) : ¬∃ f : G → ℤ, IsSDS 372100 370972 f :=
  abelian_short_linear G 47 7919 33 0 1 0 372100 370972 24 7906 1 1
    ⟨⟨(-7919),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_796321_795664_794536 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=796321) : ¬∃ f : G → ℤ, IsSDS 795664 794536 f :=
  abelian_short_linear G 47 16943 33 0 1 0 795664 794536 24 16924 1 1
    ⟨⟨(-16943),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_796321_1129_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=796321) : ¬∃ f : G → ℤ, IsSDS 1129 1 f :=
  abelian_short_linear G 47 16943 33 2 1 0 1129 1 24 19 1 1
    ⟨⟨0,0,1,(-139)⟩,[0,0,470,1128,2068,3290,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3290,2068,1128,470,0],0⟩ hG (by decide +kernel)

theorem fixed_47_24_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=47*m)
    (hm : 47 < m) (hn : k-l=(47:ℤ)*24) : False := by
  let : Fact (Nat.Prime 47) := ⟨by decide⟩
  have row := endpoint_case (s:=24) hf hg hn (by decide) hm grid_47_24
  simp only [keep_47_24,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1156 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7849_1156_28 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1177 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28153_1177_49 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=26980 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28153_26980_25852 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1129 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_54097_1129_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1129 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_372193_1129_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=372100 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_372193_372100_370972 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1129 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_796321_1129_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=795664 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_796321_795664_794536 G hg ⟨f,hf⟩

end Signed39.Contraction
