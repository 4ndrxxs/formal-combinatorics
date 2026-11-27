import SignedNineData
import SignedCenteredCertificate
import SignedBudgetCertificate
import Signed559Analytic

/-! Fixed prime subcase of the norm 9p theorem. -/

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

private theorem nine_13_23_185 (hg : Fintype.card G=299) : ¬ ∃ f : G → ℤ, IsSDS 185 68 f :=
  abelian_centered_exclusion G 13 23 185 68 9 11 10 1 0 ⟨8,(-1),0,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_13_23_198 (hg : Fintype.card G=299) : ¬ ∃ f : G → ℤ, IsSDS 198 81 f :=
  abelian_centered_exclusion G 13 23 198 81 9 12 10 1 0 ⟨8,(-1),0,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_13_27_121 (hg : Fintype.card G=351) : ¬ ∃ f : G → ℤ, IsSDS 121 4 f :=
  abelian_centered_exclusion G 13 27 121 4 9 3 10 1 0 ⟨0,(-975),154,67⟩
    (fun r => [0,0,0,0,364,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_13_27_134 (hg : Fintype.card G=351) : ¬ ∃ f : G → ℤ, IsSDS 134 17 f :=
  abelian_centered_exclusion G 13 27 134 17 9 6 10 1 0 ⟨0,(-236860),30063,17316⟩
    (fun r => [0,0,0,0,189488,0,0,118430,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_13_27_186 (hg : Fintype.card G=351) : ¬ ∃ f : G → ℤ, IsSDS 186 69 f :=
  abelian_centered_exclusion G 13 27 186 69 9 12 10 1 0 ⟨(-14928),0,957,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,1555,0].getD r 0) hg (by decide +kernel)

private theorem nine_13_27_225 (hg : Fintype.card G=351) : ¬ ∃ f : G → ℤ, IsSDS 225 108 f :=
  abelian_centered_exclusion G 13 27 225 108 9 15 10 1 0 ⟨(-6),(-1),1,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_13_27_329 (hg : Fintype.card G=351) : ¬ ∃ f : G → ℤ, IsSDS 329 212 f :=
  abelian_centered_exclusion G 13 27 329 212 9 21 10 1 0 ⟨432,(-43),0,1⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_13_79_121 (hg : Fintype.card G=1027) : ¬ ∃ f : G → ℤ, IsSDS 121 4 f :=
  abelian_centered_exclusion G 13 79 121 4 9 5 10 1 0 ⟨(-3835),(-52),140,3⟩
    (fun r => [3835,104,0,0,0,520,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_13_79_1018 (hg : Fintype.card G=1027) : ¬ ∃ f : G → ℤ, IsSDS 1018 901 f :=
  abelian_centered_exclusion G 13 79 1018 901 9 74 10 1 0 ⟨(-79),1,0,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_13_199_118 (hg : Fintype.card G=2587) : ¬ ∃ f : G → ℤ, IsSDS 118 1 f :=
  abelian_centered_exclusion G 13 199 118 1 9 4 10 1 0 ⟨(-364),(-39),21,(-2)⟩
    (fun r => [364,0,156,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_13_823_118 (hg : Fintype.card G=10699) : ¬ ∃ f : G → ℤ, IsSDS 118 1 f :=
  abelian_short_linear G 13 823 10 0 1 0 118 1 9 8 8 11
    ⟨⟨(-936),(-182),33,0⟩,[936,364,0,0,0,156,0,0,0,0,0,0,0],0⟩ hg (by decide +kernel)

private theorem nine_13_823_10609 (hg : Fintype.card G=10699) : ¬ ∃ f : G → ℤ, IsSDS 10609 10492 f :=
  abelian_centered_exclusion G 13 823 10609 10492 9 815 10 1 0 ⟨(-823),1,0,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

theorem fixed_nine_13 {m : ℕ} {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f) (hG : Fintype.card G=13*m)
    (hm : 13 < m) (hn : k-lam=(13:ℤ)*9) : False := by
  have h := listed9 hf hG hm hn (by decide) (B:=1063) (by intro t ht; omega) grid_13
  simp only [nineList,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 221 117 17 13 2 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 221 117 17 13 2 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=185 := by omega
    rw [hk,hL] at hf
    exact nine_13_23_185 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=198 := by omega
    rw [hk,hL] at hf
    exact nine_13_23_198 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=121 := by omega
    rw [hk,hL] at hf
    exact nine_13_27_121 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=134 := by omega
    rw [hk,hL] at hf
    exact nine_13_27_134 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=186 := by omega
    rw [hk,hL] at hf
    exact nine_13_27_186 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=225 := by omega
    rw [hk,hL] at hf
    exact nine_13_27_225 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=329 := by omega
    rw [hk,hL] at hf
    exact nine_13_27_329 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 377 117 29 13 7 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 377 117 29 13 7 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=118 := by omega
    rw [hk,hL] at hf
    exact Signed39.FiveFiftyNine.no_abelian_559_118_1 G hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 663 117 17 13 2 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 663 117 17 13 2 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=121 := by omega
    rw [hk,hL] at hf
    exact nine_13_79_121 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=1018 := by omega
    rw [hk,hL] at hf
    exact nine_13_79_1018 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 1131 117 29 13 7 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 1131 117 29 13 7 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 1989 117 17 13 2 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 1989 117 17 13 2 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 2041 117 157 13 3 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 2041 117 157 13 3 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=118 := by omega
    rw [hk,hL] at hf
    exact nine_13_199_118 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 3393 117 29 13 7 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 3393 117 29 13 7 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 5967 117 17 13 2 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 5967 117 17 13 2 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=118 := by omega
    rw [hk,hL] at hf
    exact nine_13_823_118 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=10609 := by omega
    rw [hk,hL] at hf
    exact nine_13_823_10609 hG ⟨f,hf⟩

#print axioms fixed_nine_13

end Signed39.Contraction
