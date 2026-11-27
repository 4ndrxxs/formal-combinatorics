import SignedNineData
import SignedCenteredCertificate

/-! Fixed prime subcase of the norm 9p theorem. -/

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

private theorem nine_17_19_225 (hg : Fintype.card G=323) : ¬ ∃ f : G → ℤ, IsSDS 225 72 f :=
  abelian_centered_exclusion G 17 19 225 72 9 9 12 3 8 ⟨0,(-3),1,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_17_19_242 (hg : Fintype.card G=323) : ¬ ∃ f : G → ℤ, IsSDS 242 89 f :=
  abelian_centered_exclusion G 17 19 242 89 9 10 12 3 8 ⟨(-19),1,0,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_17_59_154 (hg : Fintype.card G=1003) : ¬ ∃ f : G → ℤ, IsSDS 154 1 f :=
  abelian_centered_exclusion G 17 59 154 1 9 2 12 3 8 ⟨(-595),0,12,7⟩
    (fun r => [0,0,255,0,0,0,0,0,0,0,0,0,0,51,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_17_67_162 (hg : Fintype.card G=1139) : ¬ ∃ f : G → ℤ, IsSDS 162 9 f :=
  abelian_centered_exclusion G 17 67 162 9 9 6 12 3 8 ⟨0,(-561),54,37⟩
    (fun r => [0,0,0,0,0,0,306,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_17_67_1097 (hg : Fintype.card G=1139) : ¬ ∃ f : G → ℤ, IsSDS 1097 944 f :=
  abelian_centered_exclusion G 17 67 1097 944 9 61 12 3 8 ⟨(-67),1,0,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_17_83_166 (hg : Fintype.card G=1411) : ¬ ∃ f : G → ℤ, IsSDS 166 13 f :=
  abelian_centered_exclusion G 17 83 166 13 9 8 12 3 8 ⟨0,(-459),35,26⟩
    (fun r => [0,0,0,0,0,0,0,0,748,0,0,748,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_17_83_1305 (hg : Fintype.card G=1411) : ¬ ∃ f : G → ℤ, IsSDS 1305 1152 f :=
  abelian_centered_exclusion G 17 83 1305 1152 9 75 12 3 8 ⟨63,(-1),0,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_17_103_161 (hg : Fintype.card G=1751) : ¬ ∃ f : G → ℤ, IsSDS 161 8 f :=
  abelian_centered_exclusion G 17 103 161 8 9 7 12 3 8 ⟨(-11327120000),(-3217878400),409091075,261818288⟩
    (fun r => [0,0,0,0,0,0,0,2316976000,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_17_103_1674 (hg : Fintype.card G=1751) : ¬ ∃ f : G → ℤ, IsSDS 1674 1521 f :=
  abelian_centered_exclusion G 17 103 1674 1521 9 96 12 3 8 ⟨(-1),0,0,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_17_263_154 (hg : Fintype.card G=4471) : ¬ ∃ f : G → ℤ, IsSDS 154 1 f :=
  abelian_centered_exclusion G 17 263 154 1 9 4 12 3 8 ⟨(-2872357000),(-493038000),68045250,35111349⟩
    (fun r => [0,0,0,0,1929195000,0,0,1157517000,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

theorem fixed_nine_17 {m : ℕ} {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f) (hG : Fintype.card G=17*m)
    (hm : 17 < m) (hn : k-lam=(17:ℤ)*9) : False := by
  have h := listed9 hf hG hm hn (by decide) (B:=1387) (by intro t ht; omega) grid_17
  simp only [nineList,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=225 := by omega
    rw [hk,hL] at hf
    exact nine_17_19_225 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=242 := by omega
    rw [hk,hL] at hf
    exact nine_17_19_242 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 969 153 3 17 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 969 153 3 17 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=154 := by omega
    rw [hk,hL] at hf
    exact nine_17_59_154 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=162 := by omega
    rw [hk,hL] at hf
    exact nine_17_67_162 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=1097 := by omega
    rw [hk,hL] at hf
    exact nine_17_67_1097 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=166 := by omega
    rw [hk,hL] at hf
    exact nine_17_83_166 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=1305 := by omega
    rw [hk,hL] at hf
    exact nine_17_83_1305 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 1513 153 89 17 22 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 1513 153 89 17 22 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=161 := by omega
    rw [hk,hL] at hf
    exact nine_17_103_161 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=1674 := by omega
    rw [hk,hL] at hf
    exact nine_17_103_1674 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 2907 153 3 17 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 2907 153 3 17 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 3417 153 3 17 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 3417 153 3 17 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=154 := by omega
    rw [hk,hL] at hf
    exact nine_17_263_154 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 10251 153 3 17 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 10251 153 3 17 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 18343 153 13 17 3 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 18343 153 13 17 3 0 9)

#print axioms fixed_nine_17

end Signed39.Contraction
