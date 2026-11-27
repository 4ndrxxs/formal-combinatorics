import Signed24ColdPrime23Part0
import Signed24ColdPrime23Part12
import Signed24ColdPrime23Part24
import Signed24ColdPrime23Part36
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_23_24 : divisorGrid 23 24 226 qInputs_23_24 keep_23_24 := by
  intro d
  fin_cases d
  · exact slice24x23x0
  · exact slice24x23x1
  · exact slice24x23x2
  · exact slice24x23x3
  · exact slice24x23x4
  · exact slice24x23x5
  · exact slice24x23x6
  · exact slice24x23x7
  · exact slice24x23x8
  · exact slice24x23x9
  · exact slice24x23x10
  · exact slice24x23x11
  · exact slice24x23x12
  · exact slice24x23x13
  · exact slice24x23x14
  · exact slice24x23x15
  · exact slice24x23x16
  · exact slice24x23x17
  · exact slice24x23x18
  · exact slice24x23x19
  · exact slice24x23x20
  · exact slice24x23x21
  · exact slice24x23x22
  · exact slice24x23x23
  · exact slice24x23x24
  · exact slice24x23x25
  · exact slice24x23x26
  · exact slice24x23x27
  · exact slice24x23x28
  · exact slice24x23x29
  · exact slice24x23x30
  · exact slice24x23x31
  · exact slice24x23x32
  · exact slice24x23x33
  · exact slice24x23x34
  · exact slice24x23x35
  · exact slice24x23x36
  · exact slice24x23x37
  · exact slice24x23x38
  · exact slice24x23x39
  · exact slice24x23x40
  · exact slice24x23x41
  · exact slice24x23x42
  · exact slice24x23x43
  · exact slice24x23x44
  · exact slice24x23x45
  · exact slice24x23x46
  · exact slice24x23x47


private theorem frontier_mixed_25369_553_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=25369) : ¬∃ f : G → ℤ, IsSDS 553 1 f :=
  abelian_short_linear G 23 1103 22 8 1 0 553 1 24 7 12 25
    ⟨⟨(-269172312),(-11971615),7834970,(-860200)⟩,[269172312,0,0,22935094,95772920,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_88849_553_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=88849) : ¬∃ f : G → ℤ, IsSDS 553 1 f :=
  abelian_short_linear G 23 3863 22 5 1 0 553 1 24 13 12 25
    ⟨⟨(-30590),(-3726),555,(-43)⟩,[30590,9384,14904,21620,4002,13110,0,9384,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1932],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_88849_88804_88252 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=88849) : ¬∃ f : G → ℤ, IsSDS 88804 88252 f :=
  abelian_short_linear G 23 3863 22 0 1 0 88804 88252 24 3850 12 25
    ⟨⟨(-3863),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_279289_278784_278232 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=279289) : ¬∃ f : G → ℤ, IsSDS 278784 278232 f :=
  abelian_short_linear G 23 12143 22 0 1 0 278784 278232 24 12120 12 25
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_279289_553_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=279289) : ¬∃ f : G → ℤ, IsSDS 553 1 f :=
  abelian_short_linear G 23 12143 22 0 1 0 553 1 24 23 12 25
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_23_24_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=23*m)
    (hm : 23 < m) (hn : k-l=(23:ℤ)*24) : False := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have row := endpoint_case (s:=24) hf hg hn (by decide) hm grid_23_24
  simp only [keep_23_24,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=553 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_25369_553_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=553 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_88849_553_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=88804 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_88849_88804_88252 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=553 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_279289_553_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=278784 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_279289_278784_278232 G hg ⟨f,hf⟩

end Signed39.Contraction
