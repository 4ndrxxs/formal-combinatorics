import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_23_16 : ℕ → Option QuotientInput
  | 41 => some ⟨41,23,5,0,16⟩
  | 91 => some ⟨13,23,3,0,16⟩
  | 101 => some ⟨101,23,25,0,16⟩
  | 143 => some ⟨13,23,3,0,16⟩
  | 559 => some ⟨13,23,3,0,16⟩
  | 1111 => some ⟨101,23,25,0,16⟩
  | _ => none

private def keep_23_16 : List (ℕ × ℤ) := [(29,28),(43,13),(49,79),(49,608),(67,77),(67,928),(77,67),(77,1148),(79,49),(79,1268),(103,32),(103,1849),(191,1),(203,4),(367,16),(367,7721),(469,11),(469,10108),(553,7),(553,12128),(571,4),(571,12677),(737,7),(737,16268),(1123,4),(1123,25189),(1847,1),(1847,42068),(2767,1),(2767,63136),(3871,1),(3871,88436),(5159,1),(5159,117968)]

private theorem grid_23_16 : divisorGrid 23 16 149 qInputs_23_16 keep_23_16 := by decide +kernel

private theorem frontier_mixed_667_396_28 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=667) : ¬∃ f : G → ℤ, IsSDS 396 28 f :=
  abelian_short_linear G 23 29 18 0 1 0 396 28 16 6 18 25
    ⟨⟨0,(-2615550),87132,263725⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_989_381_13 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=989) : ¬∃ f : G → ℤ, IsSDS 381 13 f :=
  abelian_short_linear G 23 43 18 1 1 0 381 13 16 5 18 25
    ⟨⟨0,(-598),60,43⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1127_447_79 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1127) : ¬∃ f : G → ℤ, IsSDS 447 79 f :=
  abelian_short_linear G 23 49 18 1 1 0 447 79 16 13 18 25
    ⟨⟨0,0,313880,(-64841)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7755800,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1127_976_608 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1127) : ¬∃ f : G → ℤ, IsSDS 976 608 f :=
  abelian_short_linear G 23 49 18 0 1 0 976 608 16 36 18 25
    ⟨⟨(-49),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1541_445_77 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1541) : ¬∃ f : G → ℤ, IsSDS 445 77 f :=
  abelian_short_linear G 23 67 18 1 1 0 445 77 16 15 18 25
    ⟨⟨0,(-650713240),101484600,22449413⟩,[0,0,0,0,0,0,254626920,106094550,0,0,0,77802670,0,0,650713240,954850950,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1541_1296_928 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1541) : ¬∃ f : G → ℤ, IsSDS 1296 928 f :=
  abelian_short_linear G 23 67 18 0 1 0 1296 928 16 52 18 25
    ⟨⟨600990,(-26887),899,254⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1771_435_67 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1771) : ¬∃ f : G → ℤ, IsSDS 435 67 f :=
  abelian_short_linear G 23 77 18 1 1 0 435 67 16 15 18 25
    ⟨⟨0,(-46),15,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1771_1516_1148 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1771) : ¬∃ f : G → ℤ, IsSDS 1516 1148 f :=
  abelian_short_linear G 23 77 18 0 1 0 1516 1148 16 62 18 25
    ⟨⟨3927,(-128),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1817_417_49 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1817) : ¬∃ f : G → ℤ, IsSDS 417 49 f :=
  abelian_short_linear G 23 79 18 1 1 0 417 49 16 13 18 25
    ⟨⟨(-1627422000),(-135608550),67106600,6070097⟩,[1627422000,0,0,0,0,0,0,0,112236000,0,0,0,0,334369750,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1817_1636_1268 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1817) : ¬∃ f : G → ℤ, IsSDS 1636 1268 f :=
  abelian_short_linear G 23 79 18 0 1 0 1636 1268 16 66 18 25
    ⟨⟨4345,(-134),0,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2369_400_32 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2369) : ¬∃ f : G → ℤ, IsSDS 400 32 f :=
  abelian_short_linear G 23 103 18 2 1 0 400 32 16 12 18 25
    ⟨⟨0,(-6561552),846954,258686⟩,[0,0,0,0,0,0,0,0,0,0,14353395,0,0,0,0,12302910,4921164,410097,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2369_2217_1849 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2369) : ¬∃ f : G → ℤ, IsSDS 2217 1849 f :=
  abelian_short_linear G 23 103 18 0 1 0 2217 1849 16 91 18 25
    ⟨⟨(-103),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4393_369_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4393) : ¬∃ f : G → ℤ, IsSDS 369 1 f :=
  abelian_short_linear G 23 191 18 4 1 0 369 1 16 3 18 25
    ⟨⟨(-7728),(-115),231,(-10)⟩,[7728,230,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4669_372_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4669) : ¬∃ f : G → ℤ, IsSDS 372 4 f :=
  abelian_short_linear G 23 203 18 4 1 0 372 4 16 6 18 25
    ⟨⟨0,(-414077510),31310110,16829582⟩,[0,0,0,0,72013480,0,0,477089305,0,0,0,45008425,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8441_384_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8441) : ¬∃ f : G → ℤ, IsSDS 384 16 f :=
  abelian_short_linear G 23 367 18 0 1 0 384 16 16 16 18 25
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8441_8089_7721 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8441) : ¬∃ f : G → ℤ, IsSDS 8089 7721 f :=
  abelian_short_linear G 23 367 18 0 1 0 8089 7721 16 351 18 25
    ⟨⟨(-367),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10787_379_11 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10787) : ¬∃ f : G → ℤ, IsSDS 379 11 f :=
  abelian_short_linear G 23 469 18 0 1 0 379 11 16 15 18 25
    ⟨⟨0,(-9),5,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10787_10476_10108 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10787) : ¬∃ f : G → ℤ, IsSDS 10476 10108 f :=
  abelian_short_linear G 23 469 18 0 1 0 10476 10108 16 454 18 25
    ⟨⟨(-469),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12719_375_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12719) : ¬∃ f : G → ℤ, IsSDS 375 7 f :=
  abelian_short_linear G 23 553 18 1 1 0 375 7 16 13 18 25
    ⟨⟨0,0,1,(-47)⟩,[0,0,138,368,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,368,138,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_12719_12496_12128 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=12719) : ¬∃ f : G → ℤ, IsSDS 12496 12128 f :=
  abelian_short_linear G 23 553 18 0 1 0 12496 12128 16 540 18 25
    ⟨⟨(-553),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13133_372_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13133) : ¬∃ f : G → ℤ, IsSDS 372 4 f :=
  abelian_short_linear G 23 571 18 3 1 0 372 4 16 10 18 25
    ⟨⟨0,0,36,(-37)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13133_13045_12677 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13133) : ¬∃ f : G → ℤ, IsSDS 13045 12677 f :=
  abelian_short_linear G 23 571 18 0 1 0 13045 12677 16 561 18 25
    ⟨⟨(-571),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_16951_375_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=16951) : ¬∃ f : G → ℤ, IsSDS 375 7 f :=
  abelian_short_linear G 23 737 18 0 1 0 375 7 16 15 18 25
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_16951_16636_16268 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=16951) : ¬∃ f : G → ℤ, IsSDS 16636 16268 f :=
  abelian_short_linear G 23 737 18 0 1 0 16636 16268 16 722 18 25
    ⟨⟨(-737),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_25829_372_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=25829) : ¬∃ f : G → ℤ, IsSDS 372 4 f :=
  abelian_short_linear G 23 1123 18 1 1 0 372 4 16 14 18 25
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_25829_25557_25189 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=25829) : ¬∃ f : G → ℤ, IsSDS 25557 25189 f :=
  abelian_short_linear G 23 1123 18 0 1 0 25557 25189 16 1109 18 25
    ⟨⟨(-1123),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_42481_369_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=42481) : ¬∃ f : G → ℤ, IsSDS 369 1 f :=
  abelian_short_linear G 23 1847 18 3 1 0 369 1 16 9 18 25
    ⟨⟨0,0,1,(-1)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_42481_42436_42068 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=42481) : ¬∃ f : G → ℤ, IsSDS 42436 42068 f :=
  abelian_short_linear G 23 1847 18 0 1 0 42436 42068 16 1838 18 25
    ⟨⟨(-1847),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_63641_369_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=63641) : ¬∃ f : G → ℤ, IsSDS 369 1 f :=
  abelian_short_linear G 23 2767 18 2 1 0 369 1 16 11 18 25
    ⟨⟨0,0,4547,(-15000)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_63641_63504_63136 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=63641) : ¬∃ f : G → ℤ, IsSDS 63504 63136 f :=
  abelian_short_linear G 23 2767 18 0 1 0 63504 63136 16 2756 18 25
    ⟨⟨(-2767),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_89033_369_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=89033) : ¬∃ f : G → ℤ, IsSDS 369 1 f :=
  abelian_short_linear G 23 3871 18 1 1 0 369 1 16 13 18 25
    ⟨⟨0,0,9,(-67)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_89033_88804_88436 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=89033) : ¬∃ f : G → ℤ, IsSDS 88804 88436 f :=
  abelian_short_linear G 23 3871 18 0 1 0 88804 88436 16 3858 18 25
    ⟨⟨(-3871),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_118657_369_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=118657) : ¬∃ f : G → ℤ, IsSDS 369 1 f :=
  abelian_short_linear G 23 5159 18 0 1 0 369 1 16 15 18 25
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_118657_118336_117968 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=118657) : ¬∃ f : G → ℤ, IsSDS 118336 117968 f :=
  abelian_short_linear G 23 5159 18 0 1 0 118336 117968 16 5144 18 25
    ⟨⟨(-5159),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_23_16_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=23*m)
    (hm : 23 < m) (hn : k-l=(23:ℤ)*16) : False := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have row := endpoint_case (s:=16) hf hg hn (by decide) hm grid_23_16
  simp only [keep_23_16,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=396 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_667_396_28 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=381 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_989_381_13 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=447 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1127_447_79 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=976 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1127_976_608 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=445 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1541_445_77 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1296 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1541_1296_928 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=435 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1771_435_67 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1516 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1771_1516_1148 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=417 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1817_417_49 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1636 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1817_1636_1268 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=400 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2369_400_32 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2217 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2369_2217_1849 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=369 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4393_369_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=372 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4669_372_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=384 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8441_384_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=8089 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8441_8089_7721 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=379 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10787_379_11 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=10476 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10787_10476_10108 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=375 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12719_375_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=12496 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_12719_12496_12128 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=372 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13133_372_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=13045 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13133_13045_12677 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=375 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_16951_375_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=16636 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_16951_16636_16268 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=372 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_25829_372_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=25557 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_25829_25557_25189 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=369 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_42481_369_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=42436 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_42481_42436_42068 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=369 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_63641_369_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=63504 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_63641_63504_63136 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=369 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_89033_369_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=88804 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_89033_88804_88436 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=369 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_118657_369_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=118336 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_118657_118336_117968 G hg ⟨f,hf⟩

end Signed39.Contraction
