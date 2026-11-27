import SignedNineData
import SignedCenteredCertificate
import Signed95Analytic

/-! Fixed prime subcase of the norm 9p theorem. -/

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

private theorem nine_5_11_46 (hg : Fintype.card G=55) : ¬ ∃ f : G → ℤ, IsSDS 46 1 f :=
  abelian_centered_exclusion G 5 11 46 1 9 2 6 3 2 ⟨(-1),(-1),0,0⟩
    (fun r => [0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_5_19_89 (hg : Fintype.card G=95) : ¬ ∃ f : G → ℤ, IsSDS 89 44 f :=
  abelian_centered_exclusion G 5 19 89 44 9 13 6 3 2 ⟨190,(-29),0,1⟩
    (fun r => [0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_5_31_81 (hg : Fintype.card G=155) : ¬ ∃ f : G → ℤ, IsSDS 81 36 f :=
  abelian_centered_exclusion G 5 31 81 36 9 15 6 3 2 ⟨1890,(-285),27,8⟩
    (fun r => [180,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_5_31_86 (hg : Fintype.card G=155) : ¬ ∃ f : G → ℤ, IsSDS 86 41 f :=
  abelian_centered_exclusion G 5 31 86 41 9 16 6 3 2 ⟨1580,(-265),27,8⟩
    (fun r => [0,180,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_5_59_49 (hg : Fintype.card G=295) : ¬ ∃ f : G → ℤ, IsSDS 49 4 f :=
  abelian_centered_exclusion G 5 59 49 4 9 7 6 3 2 ⟨(-170),(-80),27,7⟩
    (fun r => [0,0,90,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_5_59_274 (hg : Fintype.card G=295) : ¬ ∃ f : G → ℤ, IsSDS 274 229 f :=
  abelian_centered_exclusion G 5 59 274 229 9 52 6 3 2 ⟨49,(-1),0,0⟩
    (fun r => [0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_5_71_46 (hg : Fintype.card G=355) : ¬ ∃ f : G → ℤ, IsSDS 46 1 f :=
  abelian_centered_exclusion G 5 71 46 1 9 4 6 3 2 ⟨(-520),(-10),36,(-1)⟩
    (fun r => [0,135,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_5_311_46 (hg : Fintype.card G=1555) : ¬ ∃ f : G → ℤ, IsSDS 46 1 f :=
  abelian_centered_exclusion G 5 311 46 1 9 8 6 3 2 ⟨(-170),0,13,(-3)⟩
    (fun r => [0,0,0,0,160].getD r 0) hg (by decide +kernel)

private theorem nine_5_311_1521 (hg : Fintype.card G=1555) : ¬ ∃ f : G → ℤ, IsSDS 1521 1476 f :=
  abelian_centered_exclusion G 5 311 1521 1476 9 303 6 3 2 ⟨(-1),0,0,0⟩
    (fun r => [0,0,0,0,0].getD r 0) hg (by decide +kernel)

theorem fixed_nine_5 {m : ℕ} {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f) (hG : Fintype.card G=5*m)
    (hm : 5 < m) (hn : k-lam=(5:ℤ)*9) : False := by
  have h := listed9 hf hG hm hn (by decide) (B:=415) (by intro t ht; omega) grid_5
  simp only [nineList,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 45 45 3 5 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=46 := by omega
    rw [hk,hL] at hf
    exact nine_5_11_46 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=54 := by omega
    rw [hk,hL] at hf
    exact Signed39.NinetyFive.no_abelian_95_54_9 G hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=89 := by omega
    rw [hk,hL] at hf
    exact nine_5_19_89 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 145 45 29 5 7 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 145 45 29 5 7 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=81 := by omega
    rw [hk,hL] at hf
    exact nine_5_31_81 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=86 := by omega
    rw [hk,hL] at hf
    exact nine_5_31_86 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 165 45 3 5 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 165 45 3 5 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 285 45 3 5 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 285 45 3 5 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=49 := by omega
    rw [hk,hL] at hf
    exact nine_5_59_49 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=274 := by omega
    rw [hk,hL] at hf
    exact nine_5_59_274 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=46 := by omega
    rw [hk,hL] at hf
    exact nine_5_71_46 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 495 45 3 5 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 495 45 3 5 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 855 45 3 5 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 855 45 3 5 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=46 := by omega
    rw [hk,hL] at hf
    exact nine_5_311_46 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=1521 := by omega
    rw [hk,hL] at hf
    exact nine_5_311_1521 hG ⟨f,hf⟩

#print axioms fixed_nine_5

end Signed39.Contraction
