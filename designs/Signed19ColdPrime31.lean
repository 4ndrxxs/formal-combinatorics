import Signed19ColdPrime31Part0
import Signed19ColdPrime31Part12
import Signed19ColdPrime31Part24
import Signed19ColdPrime31Part36
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification
import SignedClassicalCases

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_31_19 : divisorGrid 31 19 206 qInputs_31_19 keep_31_19 := by
  intro d
  fin_cases d
  · exact slice19x31x0
  · exact slice19x31x1
  · exact slice19x31x2
  · exact slice19x31x3
  · exact slice19x31x4
  · exact slice19x31x5
  · exact slice19x31x6
  · exact slice19x31x7
  · exact slice19x31x8
  · exact slice19x31x9
  · exact slice19x31x10
  · exact slice19x31x11
  · exact slice19x31x12
  · exact slice19x31x13
  · exact slice19x31x14
  · exact slice19x31x15
  · exact slice19x31x16
  · exact slice19x31x17
  · exact slice19x31x18
  · exact slice19x31x19
  · exact slice19x31x20
  · exact slice19x31x21
  · exact slice19x31x22
  · exact slice19x31x23
  · exact slice19x31x24
  · exact slice19x31x25
  · exact slice19x31x26
  · exact slice19x31x27
  · exact slice19x31x28
  · exact slice19x31x29
  · exact slice19x31x30
  · exact slice19x31x31
  · exact slice19x31x32
  · exact slice19x31x33
  · exact slice19x31x34
  · exact slice19x31x35
  · exact slice19x31x36
  · exact slice19x31x37


private theorem frontier_mixed_2449_628_39 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2449) : ¬∃ f : G → ℤ, IsSDS 628 39 f :=
  abelian_short_linear G 31 79 23 1 1 0 628 39 19 10 9 11
    ⟨⟨0,(-9083),1155,284⟩,[0,0,0,0,0,0,0,0,0,0,9300,0,0,0,16058,6510,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2511_774_185 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2511) : ¬∃ f : G → ℤ, IsSDS 774 185 f :=
  abelian_short_linear G 31 81 23 1 1 0 774 185 19 22 9 11
    ⟨⟨0,(-4650),851,89⟩,[0,0,0,0,0,0,0,0,868,0,0,7192,434,0,0,6324,0,0,0,0,0,0,0,2852,0,10416,0,248,0,25110,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2511_1921_1332 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2511) : ¬∃ f : G → ℤ, IsSDS 1921 1332 f :=
  abelian_short_linear G 31 81 23 0 1 0 1921 1332 19 59 9 11
    ⟨⟨(-12555),0,236,(-1)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,155,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3937_624_35 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3937) : ¬∃ f : G → ℤ, IsSDS 624 35 f :=
  abelian_short_linear G 31 127 23 2 1 0 624 35 19 12 9 11
    ⟨⟨0,(-2728),493,63⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1054,6014,0,0,0,930,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3937_3817_3228 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3937) : ¬∃ f : G → ℤ, IsSDS 3817 3228 f :=
  abelian_short_linear G 31 127 23 0 1 0 3817 3228 19 115 9 11
    ⟨⟨(-127),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4619_649_60 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4619) : ¬∃ f : G → ℤ, IsSDS 649 60 f :=
  abelian_short_linear G 31 149 23 1 1 0 649 60 19 17 9 11
    ⟨⟨0,(-14167),2376,365⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,38192,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4619_4214_3625 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4619) : ¬∃ f : G → ℤ, IsSDS 4214 3625 f :=
  abelian_short_linear G 31 149 23 0 1 0 4214 3625 19 132 9 11
    ⟨⟨(-149),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7347_602_13 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7347) : ¬∃ f : G → ℤ, IsSDS 602 13 f :=
  abelian_short_linear G 31 237 23 4 1 0 602 13 19 10 9 11
    ⟨⟨(-682),(-93),13,4⟩,[682,186,124,0,0,124,0,0,0,0,0,0,0,0,0,0,0,0,124,186,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7347_7329_6740 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7347) : ¬∃ f : G → ℤ, IsSDS 7329 6740 f :=
  abelian_short_linear G 31 237 23 0 1 0 7329 6740 19 227 9 11
    ⟨⟨(-237),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13857_609_20 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13857) : ¬∃ f : G → ℤ, IsSDS 609 20 f :=
  abelian_short_linear G 31 447 23 1 1 0 609 20 19 17 9 11
    ⟨⟨0,(-9734),420,323⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6603,2480,0,14136,3875,8928,3255,12896,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13857_13412_12823 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13857) : ¬∃ f : G → ℤ, IsSDS 13412 12823 f :=
  abelian_short_linear G 31 447 23 0 1 0 13412 12823 19 430 9 11
    ⟨⟨(-447),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_31_19_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=31*m)
    (hm : 31 < m) (hn : k-l=(31:ℤ)*19) : False := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  have row := endpoint_case (s:=19) hf hg hn (by decide) hm grid_31_19
  simp only [keep_31_19,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=628 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2449_628_39 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=774 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2511_774_185 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1921 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2511_1921_1332 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=624 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3937_624_35 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3817 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3937_3817_3228 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=649 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4619_649_60 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4214 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4619_4214_3625 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=602 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7347_602_13 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7329 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7347_7329_6740 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=609 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13857_609_20 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=13412 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13857_13412_12823 G hg ⟨f,hf⟩

end Signed39.Contraction
