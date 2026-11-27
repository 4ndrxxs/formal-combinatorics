import Signed18ColdPrime31Part0
import Signed18ColdPrime31Part12
import Signed18ColdPrime31Part24
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification
import SignedFullConjugacy

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_31_18 : divisorGrid 31 18 195 qInputs_31_18 keep_31_18 := by
  intro d
  fin_cases d
  · exact slice18x31x0
  · exact slice18x31x1
  · exact slice18x31x2
  · exact slice18x31x3
  · exact slice18x31x4
  · exact slice18x31x5
  · exact slice18x31x6
  · exact slice18x31x7
  · exact slice18x31x8
  · exact slice18x31x9
  · exact slice18x31x10
  · exact slice18x31x11
  · exact slice18x31x12
  · exact slice18x31x13
  · exact slice18x31x14
  · exact slice18x31x15
  · exact slice18x31x16
  · exact slice18x31x17
  · exact slice18x31x18
  · exact slice18x31x19
  · exact slice18x31x20
  · exact slice18x31x21
  · exact slice18x31x22
  · exact slice18x31x23
  · exact slice18x31x24
  · exact slice18x31x25
  · exact slice18x31x26
  · exact slice18x31x27
  · exact slice18x31x28
  · exact slice18x31x29
  · exact slice18x31x30
  · exact slice18x31x31
  · exact slice18x31x32
  · exact slice18x31x33
  · exact slice18x31x34
  · exact slice18x31x35


private theorem frontier_mixed_2449_577_19 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2449) : ¬∃ f : G → ℤ, IsSDS 577 19 f :=
  abelian_short_linear G 31 79 23 1 3 15 577 19 18 7 25 29
    ⟨⟨(-25420000),(-775000),540000,41013⟩,[0,0,0,0,0,0,0,6277500,0,0,5580000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4681_640_82 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4681) : ¬∃ f : G → ℤ, IsSDS 640 82 f :=
  abelian_short_linear G 31 151 23 0 3 15 640 82 18 20 25 29
    ⟨⟨0,(-2728),384,65⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,8556,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1023,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4681_4081_3523 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4681) : ¬∃ f : G → ℤ, IsSDS 4081 3523 f :=
  abelian_short_linear G 31 151 23 0 3 15 4081 3523 18 131 25 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7409_560_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7409) : ¬∃ f : G → ℤ, IsSDS 560 2 f :=
  abelian_short_linear G 31 239 23 4 3 15 560 2 18 4 25 29
    ⟨⟨(-7000),(-1000),243,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_30473_560_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=30473) : ¬∃ f : G → ℤ, IsSDS 560 2 f :=
  abelian_short_linear G 31 983 23 5 3 15 560 2 18 8 25 29
    ⟨⟨(-8122),(-713),135,(-16)⟩,[0,0,5022,0,0,2232,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_31_18_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=31*m)
    (hm : 31 < m) (hn : k-l=(31:ℤ)*18) : False := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  have row := endpoint_case (s:=18) hf hg hn (by decide) hm grid_31_18
  simp only [keep_31_18,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=577 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2449_577_19 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=640 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4681_640_82 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4081 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4681_4081_3523 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=560 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7409_560_2 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=560 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_30473_560_2 G hg ⟨f,hf⟩

end Signed39.Contraction
