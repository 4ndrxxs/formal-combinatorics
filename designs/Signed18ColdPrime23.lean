import Signed18ColdPrime23Part0
import Signed18ColdPrime23Part12
import Signed18ColdPrime23Part24
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification
import SignedFullConjugacy

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_23_18 : divisorGrid 23 18 168 qInputs_23_18 keep_23_18 := by
  intro d
  fin_cases d
  · exact slice18x23x0
  · exact slice18x23x1
  · exact slice18x23x2
  · exact slice18x23x3
  · exact slice18x23x4
  · exact slice18x23x5
  · exact slice18x23x6
  · exact slice18x23x7
  · exact slice18x23x8
  · exact slice18x23x9
  · exact slice18x23x10
  · exact slice18x23x11
  · exact slice18x23x12
  · exact slice18x23x13
  · exact slice18x23x14
  · exact slice18x23x15
  · exact slice18x23x16
  · exact slice18x23x17
  · exact slice18x23x18
  · exact slice18x23x19
  · exact slice18x23x20
  · exact slice18x23x21
  · exact slice18x23x22
  · exact slice18x23x23
  · exact slice18x23x24
  · exact slice18x23x25
  · exact slice18x23x26
  · exact slice18x23x27
  · exact slice18x23x28
  · exact slice18x23x29
  · exact slice18x23x30
  · exact slice18x23x31
  · exact slice18x23x32
  · exact slice18x23x33
  · exact slice18x23x34
  · exact slice18x23x35


private theorem frontier_mixed_1127_684_270 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1127) : ¬∃ f : G → ℤ, IsSDS 684 270 f :=
  abelian_short_linear G 23 49 19 0 1 0 684 270 18 24 16 25
    ⟨⟨0,0,1969008,(-3071407)⟩,[0,0,0,0,0,0,0,57966864,0,0,0,322440681,347801184,438374409,0,0,0,818781954,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1127_707_293 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1127) : ¬∃ f : G → ℤ, IsSDS 707 293 f :=
  abelian_short_linear G 23 49 19 0 1 0 707 293 18 25 16 25
    ⟨⟨17,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1817_449_35 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1817) : ¬∃ f : G → ℤ, IsSDS 449 35 f :=
  abelian_short_linear G 23 79 19 1 1 0 449 35 18 11 16 25
    ⟨⟨0,(-23000),4000,943⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,40250,23000,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1817_1760_1346 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1817) : ¬∃ f : G → ℤ, IsSDS 1760 1346 f :=
  abelian_short_linear G 23 79 19 0 1 0 1760 1346 18 68 16 25
    ⟨⟨79,3,(-4),0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4393_441_27 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4393) : ¬∃ f : G → ℤ, IsSDS 441 27 f :=
  abelian_short_linear G 23 191 19 2 1 0 441 27 18 15 16 25
    ⟨⟨0,(-2858296020),365162720,87677577⟩,[0,0,0,0,0,0,0,0,0,0,0,7321936380,0,1527034860,0,0,0,978868500,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4393_4144_3730 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4393) : ¬∃ f : G → ℤ, IsSDS 4144 3730 f :=
  abelian_short_linear G 23 191 19 0 1 0 4144 3730 18 176 16 25
    ⟨⟨(-191),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12719_419_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12719) : ¬∃ f : G → ℤ, IsSDS 419 5 f :=
  abelian_short_linear G 23 553 19 3 1 0 419 5 18 11 16 25
    ⟨⟨(-329253750),(-38561250),6180000,488838⟩,[329253750,77122500,96403125,102830000,96403125,77122500,44988125,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12719_12632_12218 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12719) : ¬∃ f : G → ℤ, IsSDS 12632 12218 f :=
  abelian_short_linear G 23 553 19 0 1 0 12632 12218 18 542 16 25
    ⟨⟨(-553),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_16721_416_2 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=16721) : ¬∃ f : G → ℤ, IsSDS 416 2 f :=
  abelian_short_linear G 23 727 19 5 1 0 416 2 18 8 16 25
    ⟨⟨(-1535142375),(-112634496),27897896,0⟩,[1535142375,225268992,0,627702660,0,0,0,0,0,328248180,0,154511424,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_23_18_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=23*m)
    (hm : 23 < m) (hn : k-l=(23:ℤ)*18) : False := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have row := endpoint_case (s:=18) hf hg hn (by decide) hm grid_23_18
  simp only [keep_23_18,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=684 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1127_684_270 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=707 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1127_707_293 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=449 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1817_449_35 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1760 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1817_1760_1346 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4393_441_27 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4144 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4393_4144_3730 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=419 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12719_419_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=12632 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12719_12632_12218 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=416 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_16721_416_2 G hg ⟨f,hf⟩

end Signed39.Contraction
