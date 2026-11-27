import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification
import SignedMixedCases3
import SignedClassicalCases

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_3_13 : ℕ → Option QuotientInput
  | 19 => some ⟨19,3,9,0,13⟩
  | 25 => some ⟨5,3,2,0,13⟩
  | 31 => some ⟨31,3,15,0,13⟩
  | 35 => some ⟨7,13,1,0,3⟩
  | 41 => some ⟨41,3,4,0,13⟩
  | 49 => some ⟨7,13,1,0,3⟩
  | 61 => some ⟨61,3,5,0,13⟩
  | 67 => some ⟨67,3,11,0,13⟩
  | 95 => some ⟨5,3,2,0,13⟩
  | 115 => some ⟨5,3,2,0,13⟩
  | 175 => some ⟨7,13,1,0,3⟩
  | 247 => some ⟨19,3,9,0,13⟩
  | 287 => some ⟨7,13,1,0,3⟩
  | _ => none

private def keep_3_13 : List (ℕ × ℤ) := [(13,(-1)),(23,10),(23,25),(179,1),(179,490),(419,1),(419,1186)]

private theorem grid_3_13 : divisorGrid 3 13 44 qInputs_3_13 keep_3_13 := by decide +kernel

private def types_frontier_mixed_39_38_neg1 : List RowType := [((-5),13),((-1),13),(0,12),(1,13),(5,13)]
private def stage_0_frontier_mixed_39_38_neg1 : Stage := [
  (((-5),13),⟨⟨0,(-5),0,1⟩,[0,4,0],0⟩),
  (((-1),13),⟨⟨0,(-4),0,(-1)⟩,[0,5,45],0⟩),
  ((1,13),⟨⟨0,4,0,(-1)⟩,[0,45,5],0⟩),
  ((5,13),⟨⟨0,5,0,1⟩,[0,0,4],0⟩)]
private theorem frontier_mixed_39_38_neg1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=39) : ¬∃ f : G → ℤ, IsSDS 38 (-1) f :=
  abelian_short_mixed G 3 13 5 3 1 0 38 (-1) 13 0 2 17 9 2
    types_frontier_mixed_39_38_neg1 [stage_0_frontier_mixed_39_38_neg1] ⟨⟨12,0,(-1),0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_537_40_1 : List RowType := [(3,9),(3,15),(4,8),(4,14),(4,20),(5,11),(5,17),(6,12),(6,18),(7,11),(7,17),(7,23),(8,14),(8,20),(9,15),(9,21),(10,14),(10,20),(10,26),(11,17),(11,23),(12,12),(12,18),(12,24),(13,17),(13,23),(13,29)]
private def stage_0_frontier_mixed_537_40_1 : Stage := [
  ((3,9),⟨⟨88,(-19),0,1⟩,[2,2,0],0⟩),
  ((3,15),⟨⟨(-6),(-1),1,0⟩,[6,2,0],0⟩),
  ((4,8),⟨⟨(-2100),0,0,0⟩,[0,0,0],1⟩),
  ((4,14),⟨⟨(-1191190000),(-78540000),0,585000⟩,[1191190000,0,0],153153⟩),
  ((4,20),⟨⟨(-24),(-1),3,0⟩,[0,4,0],0⟩),
  ((5,11),⟨⟨(-2610),0,0,0⟩,[0,0,0],1⟩),
  ((5,17),⟨⟨66230000,(-58175000),8950000,3025000⟩,[41170000,0,0],5907⟩),
  ((6,18),⟨⟨(-4),(-1),1,0⟩,[4,0,0],0⟩),
  ((7,11),⟨⟨(-3612),0,0,0⟩,[0,0,0],1⟩),
  ((7,17),⟨⟨(-78402),(-21301),7518,917⟩,[48330,0,0],5⟩),
  ((7,23),⟨⟨(-9),0,1,0⟩,[0,1,0],0⟩),
  ((8,14),⟨⟨(-4104),0,0,0⟩,[0,0,0],1⟩),
  ((8,20),⟨⟨(-97839789),(-44525892),14060808,1806696⟩,[41596557,0,0],11456⟩),
  ((9,21),⟨⟨(-4),(-1),1,0⟩,[4,0,0],0⟩),
  ((10,14),⟨⟨(-5070),0,0,0⟩,[0,0,0],1⟩),
  ((10,20),⟨⟨(-24),(-1),3,0⟩,[0,4,0],0⟩),
  ((10,26),⟨⟨(-9),0,1,0⟩,[0,1,0],0⟩),
  ((11,17),⟨⟨3222,(-9845),0,737⟩,[8592,0,0],2⟩),
  ((11,23),⟨⟨(-12),(-1),2,0⟩,[0,0,0],0⟩),
  ((12,12),⟨⟨(-7824),0,0,0⟩,[1812,0,0],1⟩),
  ((12,18),⟨⟨0,(-2148),0,48⟩,[0,0,0],1⟩),
  ((12,24),⟨⟨(-120),0,17,(-1)⟩,[60,0,0],0⟩),
  ((13,17),⟨⟨9666,(-9308),0,832⟩,[4296,0,0],1⟩),
  ((13,23),⟨⟨(-9),0,1,0⟩,[0,1,0],0⟩),
  ((13,29),⟨⟨(-9),0,1,0⟩,[0,1,0],0⟩)]
private theorem frontier_mixed_537_40_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=537) : ¬∃ f : G → ℤ, IsSDS 40 1 f :=
  abelian_short_mixed G 3 179 5 2 1 0 40 1 13 8 2 17 60 1
    types_frontier_mixed_537_40_1 [stage_0_frontier_mixed_537_40_1] ⟨⟨(-1),0,0,0⟩,[1,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_537_529_490 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=537) : ¬∃ f : G → ℤ, IsSDS 529 490 f :=
  abelian_short_linear G 3 179 5 2 1 0 529 490 13 171 2 17
    ⟨⟨(-1),0,0,0⟩,[0,0,1],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1257_40_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1257) : ¬∃ f : G → ℤ, IsSDS 40 1 f :=
  abelian_short_linear G 3 419 5 0 1 0 40 1 13 12 2 17
    ⟨⟨(-178923),0,10366,0⟩,[0,24282,8094],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1257_1225_1186 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1257) : ¬∃ f : G → ℤ, IsSDS 1225 1186 f :=
  abelian_short_linear G 3 419 5 0 1 0 1225 1186 13 407 2 17
    ⟨⟨(-12),(-1),1,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem fixed_3_13_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=3*m)
    (hm : 3 < m) (hn : k-l=(3:ℤ)*13) : False := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have row := endpoint_case (s:=13) hf hg hn (by decide) hm grid_3_13
  simp only [keep_3_13,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=38 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_39_38_neg1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=49 := by omega
    rw [hk,hL] at hf
    exact multiplier_69_49_10 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=64 := by omega
    rw [hk,hL] at hf
    exact mixed_69_64_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=40 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_537_40_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=529 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_537_529_490 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=40 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1257_40_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1257_1225_1186 G hg ⟨f,hf⟩

private def qInputs_23_13 : ℕ → Option QuotientInput
  | 25 => some ⟨5,13,2,0,23⟩
  | 29 => some ⟨29,13,7,0,23⟩
  | 31 => some ⟨31,23,5,0,13⟩
  | 37 => some ⟨37,23,6,0,13⟩
  | 47 => some ⟨47,13,23,0,23⟩
  | 71 => some ⟨71,23,7,0,13⟩
  | 89 => some ⟨89,13,44,0,23⟩
  | 97 => some ⟨97,13,48,0,23⟩
  | 145 => some ⟨5,13,2,0,23⟩
  | 149 => some ⟨149,13,74,0,23⟩
  | 155 => some ⟨5,13,2,0,23⟩
  | 163 => some ⟨163,23,9,0,13⟩
  | 185 => some ⟨5,13,2,0,23⟩
  | 277 => some ⟨277,13,23,0,23⟩
  | 281 => some ⟨281,13,140,0,23⟩
  | 355 => some ⟨5,13,2,0,23⟩
  | 557 => some ⟨557,13,278,0,23⟩
  | 815 => some ⟨5,13,2,0,23⟩
  | 925 => some ⟨5,13,2,0,23⟩
  | 1385 => some ⟨5,13,2,0,23⟩
  | 1937 => some ⟨13,23,3,0,13⟩
  | _ => none

private def keep_23_13 : List (ℕ × ℤ) := [(43,173),(43,334),(79,1),(1459,1),(1459,33190),(2287,1),(2287,52142),(3299,1),(3299,75326)]

private theorem grid_23_13 : divisorGrid 23 13 120 qInputs_23_13 keep_23_13 := by decide +kernel

private theorem frontier_mixed_989_472_173 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=989) : ¬∃ f : G → ℤ, IsSDS 472 173 f :=
  abelian_short_linear G 23 43 16 0 1 0 472 173 13 18 8 9
    ⟨⟨0,(-277999150),75543600,6647992⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,583798215,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_989_633_334 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=989) : ¬∃ f : G → ℤ, IsSDS 633 334 f :=
  abelian_short_linear G 23 43 16 0 1 0 633 334 13 25 8 9
    ⟨⟨(-12),(-1),1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1817_300_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1817) : ¬∃ f : G → ℤ, IsSDS 300 1 f :=
  abelian_short_linear G 23 79 16 2 1 0 300 1 13 2 8 9
    ⟨⟨(-920),0,33,0⟩,[920,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_33557_300_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=33557) : ¬∃ f : G → ℤ, IsSDS 300 1 f :=
  abelian_short_linear G 23 1459 16 2 1 0 300 1 13 8 8 9
    ⟨⟨761625,(-804000),45359,45359⟩,[0,0,0,0,253875,338500,0,423125,423125,0,338500,253875,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_33557_33489_33190 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=33557) : ¬∃ f : G → ℤ, IsSDS 33489 33190 f :=
  abelian_short_linear G 23 1459 16 0 1 0 33489 33190 13 1451 8 9
    ⟨⟨(-1459),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_52601_300_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=52601) : ¬∃ f : G → ℤ, IsSDS 300 1 f :=
  abelian_short_linear G 23 2287 16 1 1 0 300 1 13 10 8 9
    ⟨⟨(-5584221000),(-1127622300),114373119,0⟩,[5584221000,2255244600,1610889000,3651459000,644355600,322177800,2684815000,0,0,2684815000,322177800,644355600,0,1610889000,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_52601_52441_52142 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=52601) : ¬∃ f : G → ℤ, IsSDS 52441 52142 f :=
  abelian_short_linear G 23 2287 16 0 1 0 52441 52142 13 2277 8 9
    ⟨⟨(-2287),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_75877_300_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=75877) : ¬∃ f : G → ℤ, IsSDS 300 1 f :=
  abelian_short_linear G 23 3299 16 0 1 0 300 1 13 12 8 9
    ⟨⟨(-168176),(-30429),2610,(-583)⟩,[168176,60858,38226,100280,6900,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_75877_75625_75326 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=75877) : ¬∃ f : G → ℤ, IsSDS 75625 75326 f :=
  abelian_short_linear G 23 3299 16 0 1 0 75625 75326 13 3287 8 9
    ⟨⟨(-3299),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem fixed_23_13_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=23*m)
    (hm : 23 < m) (hn : k-l=(23:ℤ)*13) : False := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have row := endpoint_case (s:=13) hf hg hn (by decide) hm grid_23_13
  simp only [keep_23_13,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=472 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_989_472_173 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=633 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_989_633_334 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=300 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1817_300_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=300 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_33557_300_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=33489 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_33557_33489_33190 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=300 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_52601_300_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=52441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_52601_52441_52142 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=300 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_75877_300_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=75625 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_75877_75625_75326 G hg ⟨f,hf⟩

theorem no_norm_cofactor_13 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {p : ℕ} [Fact p.Prime] {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (hd : p∣Fintype.card G) (hn : k-l=(p:ℤ)*13) (hs : ¬ p∣13) : False := by
  obtain ⟨p3,ple,m,hg,hm⟩ := common_prime_bounds (s:=13) hf hd hn hs (by decide)
  have all : ∀ t : Fin 26, Nat.Prime t.val → 3≤t.val → ¬t.val∣13 → t.val=3 ∨ t.val=5 ∨ t.val=7 ∨ t.val=11 ∨ t.val=17 ∨ t.val=19 ∨ t.val=23 := by decide +kernel
  rcases all ⟨p,by omega⟩ Fact.out p3 hs with hh|hh|hh|hh|hh|hh|hh
  · change p=3 at hh; subst p
    exact fixed_3_13_false hf hg hm hn
  · change p=5 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 5 13 5 13 2 0 1)
  · change p=7 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 7 13 7 13 1 0 1)
  · change p=11 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 11 13 11 13 5 0 1)
  · change p=17 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 17 13 17 13 2 0 1)
  · change p=19 at hh; subst p
    exact prime_factor_sieve hf hd hn (by decide +kernel : quotientCertificate 19 13 19 13 9 0 1)
  · change p=23 at hh; subst p
    exact fixed_23_13_false hf hg hm hn

#print axioms no_norm_cofactor_13

end Signed39.Contraction
