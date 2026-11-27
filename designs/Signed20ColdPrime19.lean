import Signed20ColdPrime19Part0
import Signed20ColdPrime19Part12
import Signed20ColdPrime19Part24
import Signed20ColdPrime19Part36
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_19_20 : divisorGrid 19 20 170 qInputs_19_20 keep_19_20 := by
  intro d
  fin_cases d
  · exact slice20x19x0
  · exact slice20x19x1
  · exact slice20x19x2
  · exact slice20x19x3
  · exact slice20x19x4
  · exact slice20x19x5
  · exact slice20x19x6
  · exact slice20x19x7
  · exact slice20x19x8
  · exact slice20x19x9
  · exact slice20x19x10
  · exact slice20x19x11
  · exact slice20x19x12
  · exact slice20x19x13
  · exact slice20x19x14
  · exact slice20x19x15
  · exact slice20x19x16
  · exact slice20x19x17
  · exact slice20x19x18
  · exact slice20x19x19
  · exact slice20x19x20
  · exact slice20x19x21
  · exact slice20x19x22
  · exact slice20x19x23
  · exact slice20x19x24
  · exact slice20x19x25
  · exact slice20x19x26
  · exact slice20x19x27
  · exact slice20x19x28
  · exact slice20x19x29
  · exact slice20x19x30
  · exact slice20x19x31
  · exact slice20x19x32
  · exact slice20x19x33
  · exact slice20x19x34
  · exact slice20x19x35
  · exact slice20x19x36
  · exact slice20x19x37
  · exact slice20x19x38
  · exact slice20x19x39


private theorem frontier_mixed_589_429_49 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=589) : ¬∃ f : G → ℤ, IsSDS 429 49 f :=
  abelian_short_linear G 19 31 18 1 2 9 429 49 20 9 10 21
    ⟨⟨9,(-8),0,(-1)⟩,[0,0,0,0,0,56,0,96,0,144,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1121_484_104 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1121) : ¬∃ f : G → ℤ, IsSDS 484 104 f :=
  abelian_short_linear G 19 59 18 1 2 9 484 104 20 18 10 21
    ⟨⟨0,(-646),156,17⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,2280,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1121_921_541 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1121) : ¬∃ f : G → ℤ, IsSDS 921 541 f :=
  abelian_short_linear G 19 59 18 0 2 9 921 541 20 41 10 21
    ⟨⟨1995,(-152),15,2⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1349_384_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1349) : ¬∃ f : G → ℤ, IsSDS 384 4 f :=
  abelian_short_linear G 19 71 18 2 2 9 384 4 20 4 10 21
    ⟨⟨0,(-76),6,5⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1501_709_329 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1501) : ¬∃ f : G → ℤ, IsSDS 709 329 f :=
  abelian_short_linear G 19 79 18 0 2 9 709 329 20 37 10 21
    ⟨⟨(-1803),0,68,(-1)⟩,[0,0,0,696,0,0,0,0,0,0,0,0,0,0,0,0,240,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1501_804_424 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1501) : ¬∃ f : G → ℤ, IsSDS 804 424 f :=
  abelian_short_linear G 19 79 18 0 2 9 804 424 20 42 10 21
    ⟨⟨0,0,63,(-2)⟩,[494,0,0,0,0,0,722,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2869_381_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2869) : ¬∃ f : G → ℤ, IsSDS 381 1 f :=
  abelian_short_linear G 19 151 18 4 2 9 381 1 20 3 10 21
    ⟨⟨(-4085),(-76),108,13⟩,[0,152,0,1064,0,0,0,1064,0,152,0,0,0,0,0,0,608,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7201_400_20 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7201) : ¬∃ f : G → ℤ, IsSDS 400 20 f :=
  abelian_short_linear G 19 379 18 0 2 9 400 20 20 20 10 21
    ⟨⟨0,(-902),180,19⟩,[0,360,0,0,0,0,0,0,0,0,0,0,0,0,0,0,928,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7201_6841_6461 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7201) : ¬∃ f : G → ℤ, IsSDS 6841 6461 f :=
  abelian_short_linear G 19 379 18 0 2 9 6841 6461 20 359 10 21
    ⟨⟨341,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_17309_381_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=17309) : ¬∃ f : G → ℤ, IsSDS 381 1 f :=
  abelian_short_linear G 19 911 18 6 2 9 381 1 20 7 10 21
    ⟨⟨(-1215375),(-109268),30704,0⟩,[0,188904,0,655608,0,203720,0,0,0,44448,0,337064,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_60629_381_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=60629) : ¬∃ f : G → ℤ, IsSDS 381 1 f :=
  abelian_short_linear G 19 3191 18 3 2 9 381 1 20 13 10 21
    ⟨⟨(-513),(-152),18,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_60629_60516_60136 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=60629) : ¬∃ f : G → ℤ, IsSDS 60516 60136 f :=
  abelian_short_linear G 19 3191 18 0 2 9 60516 60136 20 3178 10 21
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_103949_381_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=103949) : ¬∃ f : G → ℤ, IsSDS 381 1 f :=
  abelian_short_linear G 19 5471 18 1 2 9 381 1 20 17 10 21
    ⟨⟨0,(-1368),81,5⟩,[0,0,684,0,874,0,0,0,0,0,0,0,0,0,0,684,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_103949_103684_103304 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=103949) : ¬∃ f : G → ℤ, IsSDS 103684 103304 f :=
  abelian_short_linear G 19 5471 18 0 2 9 103684 103304 20 5454 10 21
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_19_20_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=19*m)
    (hm : 19 < m) (hn : k-l=(19:ℤ)*20) : False := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  have row := endpoint_case (s:=20) hf hg hn (by decide) hm grid_19_20
  simp only [keep_19_20,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=429 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_589_429_49 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=484 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1121_484_104 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=921 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1121_921_541 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=384 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1349_384_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=709 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1501_709_329 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=804 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1501_804_424 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=381 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2869_381_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=400 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7201_400_20 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6841 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7201_6841_6461 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=381 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_17309_381_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=381 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_60629_381_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=60516 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_60629_60516_60136 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=381 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_103949_381_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=103684 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_103949_103684_103304 G hg ⟨f,hf⟩

end Signed39.Contraction
