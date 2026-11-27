import SignedBinaryFibreCases
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_3_16 : ℕ → Option QuotientInput
  | 37 => some ⟨37,3,9,0,16⟩
  | 61 => some ⟨61,3,5,0,16⟩
  | 97 => some ⟨97,3,24,0,16⟩
  | _ => none

private def keep_3_16 : List (ℕ × ℤ) := [(23,4),(47,16),(47,61),(59,1),(71,4),(71,157),(131,1),(143,4),(143,349),(227,1),(227,628),(347,1),(347,976),(491,1),(491,1396),(659,1),(659,1888)]

private theorem grid_3_16 : divisorGrid 3 16 54 qInputs_3_16 keep_3_16 := by decide +kernel

private theorem frontier_mixed_213_205_157 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=213) : ¬∃ f : G → ℤ, IsSDS 205 157 f :=
  abelian_short_linear G 3 71 5 2 2 1 205 157 16 61 2 21
    ⟨⟨57,(-1),0,0⟩,[0,0,8],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_429_52_4 : List RowType := [(10,14),(10,20),(12,12),(12,18),(14,20),(16,20),(16,26),(18,18),(18,24)]
private def stage_0_frontier_mixed_429_52_4 : Stage := [
  ((10,20),⟨⟨0,(-10),7,0⟩,[54,20,0],0⟩),
  ((12,12),⟨⟨0,0,(-1580000),0⟩,[0,0,0],3213⟩),
  ((12,18),⟨⟨0,(-5),4,0⟩,[18,0,0],0⟩),
  ((16,20),⟨⟨(-404),0,30,(-1)⟩,[188,84,0],0⟩),
  ((16,26),⟨⟨0,(-10),7,0⟩,[54,20,0],0⟩),
  ((18,18),⟨⟨(-19548),0,234,0⟩,[3996,1332,0],1⟩),
  ((18,24),⟨⟨(-4),(-1),1,0⟩,[4,0,0],0⟩)]
private theorem frontier_mixed_429_52_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=429) : ¬∃ f : G → ℤ, IsSDS 52 4 f :=
  abelian_short_mixed G 3 143 5 1 2 1 52 4 16 14 2 21 48 1
    types_frontier_mixed_429_52_4 [stage_0_frontier_mixed_429_52_4] ⟨⟨2,(-3),2,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_429_397_349 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=429) : ¬∃ f : G → ℤ, IsSDS 397 349 f :=
  abelian_short_linear G 3 143 5 1 2 1 397 349 16 129 2 21
    ⟨⟨(-1),0,0,0⟩,[0,0,1],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_681_49_1 : List RowType := [(5,11),(5,17),(5,23),(7,11),(7,17),(7,23),(7,29),(9,15),(9,21),(9,27),(11,17),(11,23),(11,29),(13,17),(13,23),(13,29),(13,35)]
private def stage_0_frontier_mixed_681_49_1 : Stage := [
  ((5,11),⟨⟨(-7950000),0,0,0⟩,[0,0,0],1297⟩),
  ((5,17),⟨⟨(-15570000),0,0,0⟩,[10270000,0,0],681⟩),
  ((5,23),⟨⟨(-4),(-1),1,0⟩,[0,0,0],0⟩),
  ((7,11),⟨⟨(-12978),0,0,0⟩,[0,0,0],1⟩),
  ((7,17),⟨⟨(-12978),0,0,0⟩,[0,0,0],1⟩),
  ((7,23),⟨⟨(-55),16,0,(-1)⟩,[0,16,0],0⟩),
  ((7,29),⟨⟨(-11),0,1,0⟩,[0,0,0],0⟩),
  ((9,27),⟨⟨(-171),0,20,(-1)⟩,[0,0,0],0⟩),
  ((11,17),⟨⟨(-13930000),0,0,0⟩,[0,0,0],1021⟩),
  ((11,23),⟨⟨(-99),20,0,(-1)⟩,[0,8,24],0⟩),
  ((11,29),⟨⟨(-11),0,1,0⟩,[0,0,0],0⟩),
  ((13,17),⟨⟨(-1990000),0,0,0⟩,[0,0,0],143⟩),
  ((13,23),⟨⟨(-38961),1885,0,0⟩,[0,0,1510],1⟩),
  ((13,29),⟨⟨(-11),0,1,0⟩,[0,0,0],0⟩),
  ((13,35),⟨⟨(-11),0,1,0⟩,[0,0,0],0⟩)]
private theorem frontier_mixed_681_49_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=681) : ¬∃ f : G → ℤ, IsSDS 49 1 f :=
  abelian_short_mixed G 3 227 5 3 2 1 49 1 16 9 2 21 76 1
    types_frontier_mixed_681_49_1 [stage_0_frontier_mixed_681_49_1] ⟨⟨81,0,0,(-1)⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_681_676_628 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=681) : ¬∃ f : G → ℤ, IsSDS 676 628 f :=
  abelian_short_linear G 3 227 5 2 2 1 676 628 16 218 2 21
    ⟨⟨224,0,(-1),0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1041_49_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1041) : ¬∃ f : G → ℤ, IsSDS 49 1 f :=
  abelian_short_linear G 3 347 5 2 2 1 49 1 16 11 2 21
    ⟨⟨(-159),20,4,(-1)⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1041_1024_976 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1041) : ¬∃ f : G → ℤ, IsSDS 1024 976 f :=
  abelian_short_linear G 3 347 5 2 2 1 1024 976 16 336 2 21
    ⟨⟨(-1),0,0,0⟩,[0,0,1],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1473_49_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1473) : ¬∃ f : G → ℤ, IsSDS 49 1 f :=
  abelian_short_linear G 3 491 5 1 2 1 49 1 16 13 2 21
    ⟨⟨(-23),0,1,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1473_1444_1396 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1473) : ¬∃ f : G → ℤ, IsSDS 1444 1396 f :=
  abelian_short_linear G 3 491 5 1 2 1 1444 1396 16 478 2 21
    ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1977_49_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1977) : ¬∃ f : G → ℤ, IsSDS 49 1 f :=
  abelian_short_linear G 3 659 5 0 2 1 49 1 16 15 2 21
    ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1977_1936_1888 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1977) : ¬∃ f : G → ℤ, IsSDS 1936 1888 f :=
  abelian_short_linear G 3 659 5 0 2 1 1936 1888 16 644 2 21
    ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_3_16_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=3*m)
    (hm : 3 < m) (hn : k-l=(3:ℤ)*16) : False := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have row := endpoint_case (s:=16) hf hg hn (by decide) hm grid_3_16
  simp only [keep_3_16,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=52 := by omega
    rw [hk,hL] at hf
    exact binary_69_52_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=64 := by omega
    rw [hk,hL] at hf
    exact binary_141_64_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=109 := by omega
    rw [hk,hL] at hf
    exact binary_141_109_61 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=49 := by omega
    rw [hk,hL] at hf
    exact binary_177_49_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=52 := by omega
    rw [hk,hL] at hf
    exact binary_213_52_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=205 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_213_205_157 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=49 := by omega
    rw [hk,hL] at hf
    exact binary_393_49_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=52 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_429_52_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=397 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_429_397_349 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=49 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_681_49_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=676 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_681_676_628 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=49 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1041_49_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1024 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1041_1024_976 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=49 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1473_49_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1444 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1473_1444_1396 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=49 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1977_49_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1936 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1977_1936_1888 G hg ⟨f,hf⟩

end Signed39.Contraction
