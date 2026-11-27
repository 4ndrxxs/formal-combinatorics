import Signed19ColdPrime3Part0
import Signed19ColdPrime3Part12
import Signed19ColdPrime3Part24
import Signed19ColdPrime3Part36
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification
import SignedClassicalCases

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_3_19 : divisorGrid 3 19 64 qInputs_3_19 keep_3_19 := by
  intro d
  fin_cases d
  · exact slice19x3x0
  · exact slice19x3x1
  · exact slice19x3x2
  · exact slice19x3x3
  · exact slice19x3x4
  · exact slice19x3x5
  · exact slice19x3x6
  · exact slice19x3x7
  · exact slice19x3x8
  · exact slice19x3x9
  · exact slice19x3x10
  · exact slice19x3x11
  · exact slice19x3x12
  · exact slice19x3x13
  · exact slice19x3x14
  · exact slice19x3x15
  · exact slice19x3x16
  · exact slice19x3x17
  · exact slice19x3x18
  · exact slice19x3x19
  · exact slice19x3x20
  · exact slice19x3x21
  · exact slice19x3x22
  · exact slice19x3x23
  · exact slice19x3x24
  · exact slice19x3x25
  · exact slice19x3x26
  · exact slice19x3x27
  · exact slice19x3x28
  · exact slice19x3x29
  · exact slice19x3x30
  · exact slice19x3x31
  · exact slice19x3x32
  · exact slice19x3x33
  · exact slice19x3x34
  · exact slice19x3x35
  · exact slice19x3x36
  · exact slice19x3x37


private theorem frontier_mixed_177_169_112 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=177) : ¬∃ f : G → ℤ, IsSDS 169 112 f :=
  abelian_short_linear G 3 59 6 3 1 0 169 112 19 47 2 25
    ⟨⟨(-1260),88,(-12),(-1)⟩,[9,0,41],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_321_289_232 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=321) : ¬∃ f : G → ℤ, IsSDS 289 232 f :=
  abelian_short_linear G 3 107 6 2 1 0 289 232 19 91 2 25
    ⟨⟨(-7740),176,0,(-1)⟩,[0,5,45],0⟩ hG (by decide +kernel)

theorem fixed_3_19_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=3*m)
    (hm : 3 < m) (hn : k-l=(3:ℤ)*19) : False := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have row := endpoint_case (s:=19) hf hg hn (by decide) hm grid_3_19
  simp only [keep_3_19,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=64 := by omega
    rw [hk,hL] at hf
    exact multiplier_177_64_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=169 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_177_169_112 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=100 := by omega
    rw [hk,hL] at hf
    exact multiplier_213_100_43 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=121 := by omega
    rw [hk,hL] at hf
    exact multiplier_213_121_64 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=64 := by omega
    rw [hk,hL] at hf
    exact multiplier_321_64_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=289 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_321_289_232 G hg ⟨f,hf⟩

end Signed39.Contraction
