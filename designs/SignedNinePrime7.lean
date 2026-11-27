import SignedNineData
import SignedCenteredCertificate

/-! Fixed prime subcase of the norm 9p theorem. -/

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

private theorem nine_7_9_62 (hg : Fintype.card G=63) : ¬ ∃ f : G → ℤ, IsSDS 62 (-1) f :=
  abelian_centered_exclusion G 7 9 62 (-1) 9 0 7 3 3 ⟨0,0,(-1),0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_19_64 (hg : Fintype.card G=133) : ¬ ∃ f : G → ℤ, IsSDS 64 1 f :=
  abelian_centered_exclusion G 7 19 64 1 9 2 7 3 3 ⟨(-10),0,1,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_27_65 (hg : Fintype.card G=189) : ¬ ∃ f : G → ℤ, IsSDS 65 2 f :=
  abelian_centered_exclusion G 7 27 65 2 9 3 7 3 3 ⟨0,(-28),3,3⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_27_72 (hg : Fintype.card G=189) : ¬ ∃ f : G → ℤ, IsSDS 72 9 f :=
  abelian_centered_exclusion G 7 27 72 9 9 6 7 3 3 ⟨0,(-17),9,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_27_100 (hg : Fintype.card G=189) : ¬ ∃ f : G → ℤ, IsSDS 100 37 f :=
  abelian_centered_exclusion G 7 27 100 37 9 12 7 3 3 ⟨(-17),0,1,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_27_121 (hg : Fintype.card G=189) : ¬ ∃ f : G → ℤ, IsSDS 121 58 f :=
  abelian_centered_exclusion G 7 27 121 58 9 15 7 3 3 ⟨(-6),(-5),3,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_27_177 (hg : Fintype.card G=189) : ¬ ∃ f : G → ℤ, IsSDS 177 114 f :=
  abelian_centered_exclusion G 7 27 177 114 9 21 7 3 3 ⟨(-27),0,1,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_29_110 (hg : Fintype.card G=203) : ¬ ∃ f : G → ℤ, IsSDS 110 47 f :=
  abelian_centered_exclusion G 7 29 110 47 9 14 7 3 3 ⟨(-2338),322,27,(-13)⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_29_117 (hg : Fintype.card G=203) : ¬ ∃ f : G → ℤ, IsSDS 117 54 f :=
  abelian_centered_exclusion G 7 29 117 54 9 15 7 3 3 ⟨(-135),24,0,(-1)⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_31_81 (hg : Fintype.card G=217) : ¬ ∃ f : G → ℤ, IsSDS 81 18 f :=
  abelian_centered_exclusion G 7 31 81 18 9 9 7 3 3 ⟨(-1827),0,108,(-1)⟩
    (fun r => [0,0,504,0,0,0,567].getD r 0) hg (by decide +kernel)

private theorem nine_7_31_172 (hg : Fintype.card G=217) : ¬ ∃ f : G → ℤ, IsSDS 172 109 f :=
  abelian_centered_exclusion G 7 31 172 109 9 22 7 3 3 ⟨16,(-1),0,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_37_90 (hg : Fintype.card G=259) : ¬ ∃ f : G → ℤ, IsSDS 90 27 f :=
  abelian_centered_exclusion G 7 37 90 27 9 12 7 3 3 ⟨(-336),0,30,(-1)⟩
    (fun r => [0,0,147,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_37_181 (hg : Fintype.card G=259) : ¬ ∃ f : G → ℤ, IsSDS 181 118 f :=
  abelian_centered_exclusion G 7 37 181 118 9 25 7 3 3 ⟨(-112),(-5),9,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_81_66 (hg : Fintype.card G=567) : ¬ ∃ f : G → ℤ, IsSDS 66 3 f :=
  abelian_centered_exclusion G 7 81 66 3 9 6 7 3 3 ⟨0,(-231),54,11⟩
    (fun r => [0,0,378,0,0,0,126].getD r 0) hg (by decide +kernel)

private theorem nine_7_81_549 (hg : Fintype.card G=567) : ¬ ∃ f : G → ℤ, IsSDS 549 486 f :=
  abelian_centered_exclusion G 7 81 549 486 9 75 7 3 3 ⟨(-79),0,1,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_83_65 (hg : Fintype.card G=581) : ¬ ∃ f : G → ℤ, IsSDS 65 2 f :=
  abelian_centered_exclusion G 7 83 65 2 9 5 7 3 3 ⟨(-497000),(-28000),36000,1323⟩
    (fun r => [0,0,189000,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_83_576 (hg : Fintype.card G=581) : ¬ ∃ f : G → ℤ, IsSDS 576 513 f :=
  abelian_centered_exclusion G 7 83 576 513 9 78 7 3 3 ⟨(-1),0,0,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_93_69 (hg : Fintype.card G=651) : ¬ ∃ f : G → ℤ, IsSDS 69 6 f :=
  abelian_centered_exclusion G 7 93 69 6 9 9 7 3 3 ⟨(-105),(-28),12,1⟩
    (fun r => [0,0,0,0,0,0,21].getD r 0) hg (by decide +kernel)

private theorem nine_7_93_594 (hg : Fintype.card G=651) : ¬ ∃ f : G → ℤ, IsSDS 594 531 f :=
  abelian_centered_exclusion G 7 93 594 531 9 84 7 3 3 ⟨(-1),0,0,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_103_64 (hg : Fintype.card G=721) : ¬ ∃ f : G → ℤ, IsSDS 64 1 f :=
  abelian_centered_exclusion G 7 103 64 1 9 4 7 3 3 ⟨(-140),(-14),9,1⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_167_65 (hg : Fintype.card G=1169) : ¬ ∃ f : G → ℤ, IsSDS 65 2 f :=
  abelian_centered_exclusion G 7 167 65 2 9 7 7 3 3 ⟨(-70),(-49),9,2⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_167_1136 (hg : Fintype.card G=1169) : ¬ ∃ f : G → ℤ, IsSDS 1136 1073 f :=
  abelian_centered_exclusion G 7 167 1136 1073 9 160 7 3 3 ⟨(-1),0,0,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_243_64 (hg : Fintype.card G=1701) : ¬ ∃ f : G → ℤ, IsSDS 64 1 f :=
  abelian_centered_exclusion G 7 243 64 1 9 6 7 3 3 ⟨0,(-42),9,1⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_243_1681 (hg : Fintype.card G=1701) : ¬ ∃ f : G → ℤ, IsSDS 1681 1618 f :=
  abelian_centered_exclusion G 7 243 1681 1618 9 237 7 3 3 ⟨(-243),1,0,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_279_65 (hg : Fintype.card G=1953) : ¬ ∃ f : G → ℤ, IsSDS 65 2 f :=
  abelian_centered_exclusion G 7 279 65 2 9 9 7 3 3 ⟨(-105),0,6,(-1)⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_279_1892 (hg : Fintype.card G=1953) : ¬ ∃ f : G → ℤ, IsSDS 1892 1829 f :=
  abelian_centered_exclusion G 7 279 1892 1829 9 270 7 3 3 ⟨(-1),0,0,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_439_64 (hg : Fintype.card G=3073) : ¬ ∃ f : G → ℤ, IsSDS 64 1 f :=
  abelian_centered_exclusion G 7 439 64 1 9 8 7 3 3 ⟨(-4718),0,171,(-37)⟩
    (fun r => [0,0,2814,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_7_439_3025 (hg : Fintype.card G=3073) : ¬ ∃ f : G → ℤ, IsSDS 3025 2962 f :=
  abelian_centered_exclusion G 7 439 3025 2962 9 431 7 3 3 ⟨(-1),0,0,0⟩
    (fun r => [0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

theorem fixed_nine_7 {m : ℕ} {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f) (hG : Fintype.card G=7*m)
    (hm : 7 < m) (hn : k-lam=(7:ℤ)*9) : False := by
  have h := listed9 hf hG hm hn (by decide) (B:=577) (by intro t ht; omega) grid_7
  simp only [nineList,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=62 := by omega
    rw [hk,hL] at hf
    exact nine_7_9_62 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=64 := by omega
    rw [hk,hL] at hf
    exact nine_7_19_64 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=65 := by omega
    rw [hk,hL] at hf
    exact nine_7_27_65 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=72 := by omega
    rw [hk,hL] at hf
    exact nine_7_27_72 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=100 := by omega
    rw [hk,hL] at hf
    exact nine_7_27_100 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=121 := by omega
    rw [hk,hL] at hf
    exact nine_7_27_121 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=177 := by omega
    rw [hk,hL] at hf
    exact nine_7_27_177 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=110 := by omega
    rw [hk,hL] at hf
    exact nine_7_29_110 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=117 := by omega
    rw [hk,hL] at hf
    exact nine_7_29_117 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=81 := by omega
    rw [hk,hL] at hf
    exact nine_7_31_81 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=172 := by omega
    rw [hk,hL] at hf
    exact nine_7_31_172 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=90 := by omega
    rw [hk,hL] at hf
    exact nine_7_37_90 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=181 := by omega
    rw [hk,hL] at hf
    exact nine_7_37_181 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=66 := by omega
    rw [hk,hL] at hf
    exact nine_7_81_66 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=549 := by omega
    rw [hk,hL] at hf
    exact nine_7_81_549 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=65 := by omega
    rw [hk,hL] at hf
    exact nine_7_83_65 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=576 := by omega
    rw [hk,hL] at hf
    exact nine_7_83_576 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=69 := by omega
    rw [hk,hL] at hf
    exact nine_7_93_69 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=594 := by omega
    rw [hk,hL] at hf
    exact nine_7_93_594 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=64 := by omega
    rw [hk,hL] at hf
    exact nine_7_103_64 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=65 := by omega
    rw [hk,hL] at hf
    exact nine_7_167_65 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=1136 := by omega
    rw [hk,hL] at hf
    exact nine_7_167_1136 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=64 := by omega
    rw [hk,hL] at hf
    exact nine_7_243_64 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=1681 := by omega
    rw [hk,hL] at hf
    exact nine_7_243_1681 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=65 := by omega
    rw [hk,hL] at hf
    exact nine_7_279_65 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=1892 := by omega
    rw [hk,hL] at hf
    exact nine_7_279_1892 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=64 := by omega
    rw [hk,hL] at hf
    exact nine_7_439_64 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=3025 := by omega
    rw [hk,hL] at hf
    exact nine_7_439_3025 hG ⟨f,hf⟩

#print axioms fixed_nine_7

end Signed39.Contraction
