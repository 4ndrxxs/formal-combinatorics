import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_29_16 : ℕ → Option QuotientInput
  | 35 => some ⟨5,29,1,0,16⟩
  | 53 => some ⟨53,29,13,0,16⟩
  | 65 => some ⟨5,29,1,0,16⟩
  | 109 => some ⟨109,29,27,0,16⟩
  | 115 => some ⟨5,29,1,0,16⟩
  | 245 => some ⟨5,29,1,0,16⟩
  | 257 => some ⟨257,29,64,0,16⟩
  | 281 => some ⟨281,29,35,0,16⟩
  | 977 => some ⟨977,29,244,0,16⟩
  | 1405 => some ⟨5,29,1,0,16⟩
  | 1417 => some ⟨109,29,27,0,16⟩
  | 4885 => some ⟨5,29,1,0,16⟩
  | _ => none

private def keep_29_16 : List (ℕ × ℤ) := [(49,5),(59,332),(59,535),(67,140),(67,1039),(103,28),(103,2435),(239,35),(239,5980),(283,23),(283,7360),(463,16),(463,12515),(499,7),(499,13840),(709,1),(721,4),(721,20333),(2333,1),(2333,67136),(3493,1),(3493,100660),(6509,1),(6509,187892)]

private theorem grid_29_16 : divisorGrid 29 16 167 qInputs_29_16 keep_29_16 := by decide +kernel

private theorem frontier_mixed_1421_469_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1421) : ¬∃ f : G → ℤ, IsSDS 469 5 f :=
  abelian_short_linear G 29 49 21 1 2 14 469 5 16 3 10 11
    ⟨⟨(-33),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1711_796_332 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1711) : ¬∃ f : G → ℤ, IsSDS 796 332 f :=
  abelian_short_linear G 29 59 21 0 2 14 796 332 16 26 10 11
    ⟨⟨24,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1711_999_535 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1711) : ¬∃ f : G → ℤ, IsSDS 999 535 f :=
  abelian_short_linear G 29 59 21 0 2 14 999 535 16 33 10 11
    ⟨⟨(-51),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1943_604_140 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1943) : ¬∃ f : G → ℤ, IsSDS 604 140 f :=
  abelian_short_linear G 29 67 21 1 2 14 604 140 16 18 10 11
    ⟨⟨0,(-575679),45810,17052⟩,[0,0,0,0,472352,0,0,0,0,0,0,0,0,0,2243672,0,0,0,0,0,0,0,0,0,1062792,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1943_1503_1039 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1943) : ¬∃ f : G → ℤ, IsSDS 1503 1039 f :=
  abelian_short_linear G 29 67 21 0 2 14 1503 1039 16 49 10 11
    ⟨⟨2479,(-104),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2987_492_28 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2987) : ¬∃ f : G → ℤ, IsSDS 492 28 f :=
  abelian_short_linear G 29 103 21 1 2 14 492 28 16 10 10 11
    ⟨⟨0,(-290),24,13⟩,[0,0,0,0,0,0,0,0,0,0,0,0,696,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2987_2899_2435 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2987) : ¬∃ f : G → ℤ, IsSDS 2899 2435 f :=
  abelian_short_linear G 29 103 21 0 2 14 2899 2435 16 93 10 11
    ⟨⟨(-103),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6931_499_35 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6931) : ¬∃ f : G → ℤ, IsSDS 499 35 f :=
  abelian_short_linear G 29 239 21 0 2 14 499 35 16 17 10 11
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6931_6444_5980 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6931) : ¬∃ f : G → ℤ, IsSDS 6444 5980 f :=
  abelian_short_linear G 29 239 21 0 2 14 6444 5980 16 222 10 11
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8207_487_23 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8207) : ¬∃ f : G → ℤ, IsSDS 487 23 f :=
  abelian_short_linear G 29 283 21 0 2 14 487 23 16 15 10 11
    ⟨⟨(-33),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8207_7824_7360 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8207) : ¬∃ f : G → ℤ, IsSDS 7824 7360 f :=
  abelian_short_linear G 29 283 21 0 2 14 7824 7360 16 268 10 11
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13427_480_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13427) : ¬∃ f : G → ℤ, IsSDS 480 16 f :=
  abelian_short_linear G 29 463 21 0 2 14 480 16 16 16 10 11
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13427_12979_12515 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13427) : ¬∃ f : G → ℤ, IsSDS 12979 12515 f :=
  abelian_short_linear G 29 463 21 0 2 14 12979 12515 16 447 10 11
    ⟨⟨(-463),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14471_471_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14471) : ¬∃ f : G → ℤ, IsSDS 471 7 f :=
  abelian_short_linear G 29 499 21 2 2 14 471 7 16 11 10 11
    ⟨⟨0,(-145),21,(-76)⟩,[0,0,0,0,0,0,0,2030,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14471_14304_13840 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14471) : ¬∃ f : G → ℤ, IsSDS 14304 13840 f :=
  abelian_short_linear G 29 499 21 0 2 14 14304 13840 16 488 10 11
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20561_465_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20561) : ¬∃ f : G → ℤ, IsSDS 465 1 f :=
  abelian_short_linear G 29 709 21 5 2 14 465 1 16 5 10 11
    ⟨⟨(-435605280),(-17008500),7177587,0⟩,[0,34017000,0,0,0,215441000,0,0,0,64249500,0,45356000,0,0,0,0,0,0,0,0,0,0,0,0,45356000,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20909_468_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20909) : ¬∃ f : G → ℤ, IsSDS 468 4 f :=
  abelian_short_linear G 29 721 21 3 2 14 468 4 16 10 10 11
    ⟨⟨0,0,3085,(-5491)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20909_20797_20333 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20909) : ¬∃ f : G → ℤ, IsSDS 20797 20333 f :=
  abelian_short_linear G 29 721 21 0 2 14 20797 20333 16 711 10 11
    ⟨⟨(-721),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_67657_465_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=67657) : ¬∃ f : G → ℤ, IsSDS 465 1 f :=
  abelian_short_linear G 29 2333 21 3 2 14 465 1 16 9 10 11
    ⟨⟨0,(-2465),504,(-1201)⟩,[0,0,0,0,0,0,0,0,0,44370,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_67657_67600_67136 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=67657) : ¬∃ f : G → ℤ, IsSDS 67600 67136 f :=
  abelian_short_linear G 29 2333 21 0 2 14 67600 67136 16 2324 10 11
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_101297_465_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=101297) : ¬∃ f : G → ℤ, IsSDS 465 1 f :=
  abelian_short_linear G 29 3493 21 2 2 14 465 1 16 11 10 11
    ⟨⟨0,0,463423,(-1270000)⟩,[0,0,0,0,0,0,0,18245000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_101297_101124_100660 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=101297) : ¬∃ f : G → ℤ, IsSDS 101124 100660 f :=
  abelian_short_linear G 29 3493 21 0 2 14 101124 100660 16 3482 10 11
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_188761_465_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=188761) : ¬∃ f : G → ℤ, IsSDS 465 1 f :=
  abelian_short_linear G 29 6509 21 0 2 14 465 1 16 15 10 11
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_188761_188356_187892 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=188761) : ¬∃ f : G → ℤ, IsSDS 188356 187892 f :=
  abelian_short_linear G 29 6509 21 0 2 14 188356 187892 16 6494 10 11
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_29_16_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=29*m)
    (hm : 29 < m) (hn : k-l=(29:ℤ)*16) : False := by
  let : Fact (Nat.Prime 29) := ⟨by decide⟩
  have row := endpoint_case (s:=16) hf hg hn (by decide) hm grid_29_16
  simp only [keep_29_16,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=469 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1421_469_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=796 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1711_796_332 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=999 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1711_999_535 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=604 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1943_604_140 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1503 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1943_1503_1039 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=492 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2987_492_28 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2899 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2987_2899_2435 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=499 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6931_499_35 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=6444 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6931_6444_5980 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=487 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8207_487_23 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7824 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8207_7824_7360 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=480 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13427_480_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=12979 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13427_12979_12515 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=471 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14471_471_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=14304 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14471_14304_13840 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=465 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20561_465_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=468 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20909_468_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=20797 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20909_20797_20333 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=465 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_67657_465_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=67600 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_67657_67600_67136 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=465 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_101297_465_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=101124 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_101297_101124_100660 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=465 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_188761_465_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=188356 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_188761_188356_187892 G hg ⟨f,hf⟩

end Signed39.Contraction
