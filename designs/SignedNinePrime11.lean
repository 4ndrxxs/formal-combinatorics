import SignedNineData
import SignedCenteredCertificate

/-! Fixed prime subcase of the norm 9p theorem. -/

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

private theorem nine_11_19_113 (hg : Fintype.card G=209) : ¬ ∃ f : G → ℤ, IsSDS 113 14 f :=
  abelian_centered_exclusion G 11 19 113 14 9 5 9 1 0 ⟨0,(-407),42,47⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_25_162 (hg : Fintype.card G=275) : ¬ ∃ f : G → ℤ, IsSDS 162 63 f :=
  abelian_centered_exclusion G 11 25 162 63 9 12 9 1 0 ⟨114,(-25),0,1⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_25_173 (hg : Fintype.card G=275) : ¬ ∃ f : G → ℤ, IsSDS 173 74 f :=
  abelian_centered_exclusion G 11 25 173 74 9 13 9 1 0 ⟨(-6),(-1),1,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_35_100 (hg : Fintype.card G=385) : ¬ ∃ f : G → ℤ, IsSDS 100 1 f :=
  abelian_centered_exclusion G 11 35 100 1 9 2 9 1 0 ⟨(-462),(-55),30,7⟩
    (fun r => [462,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_35_144 (hg : Fintype.card G=385) : ¬ ∃ f : G → ℤ, IsSDS 144 45 f :=
  abelian_centered_exclusion G 11 35 144 45 9 12 9 1 0 ⟨(-192183537),0,9104249,110617⟩
    (fun r => [0,0,0,0,0,0,24327030,13785317,0,64872080,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_35_265 (hg : Fintype.card G=385) : ¬ ∃ f : G → ℤ, IsSDS 265 166 f :=
  abelian_centered_exclusion G 11 35 265 166 9 23 9 1 0 ⟨462,0,17,(-3)⟩
    (fun r => [0,0,0,0,1056,0,0,0,264,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_43_108 (hg : Fintype.card G=473) : ¬ ∃ f : G → ℤ, IsSDS 108 9 f :=
  abelian_centered_exclusion G 11 43 108 9 9 6 9 1 0 ⟨(-6),(-43),9,2⟩
    (fun r => [6,0,0,0,0,0,0,56,6,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_43_449 (hg : Fintype.card G=473) : ¬ ∃ f : G → ℤ, IsSDS 449 350 f :=
  abelian_centered_exclusion G 11 43 449 350 9 37 9 1 0 ⟨(-215),(-2),7,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_49_117 (hg : Fintype.card G=539) : ¬ ∃ f : G → ℤ, IsSDS 117 18 f :=
  abelian_centered_exclusion G 11 49 117 18 9 9 9 1 0 ⟨0,(-22),6,1⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_49_458 (hg : Fintype.card G=539) : ¬ ∃ f : G → ℤ, IsSDS 458 359 f :=
  abelian_centered_exclusion G 11 49 458 359 9 40 9 1 0 ⟨1617,(-82),0,1⟩
    (fun r => [0,15,0,39,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_133_101 (hg : Fintype.card G=1463) : ¬ ∃ f : G → ℤ, IsSDS 101 2 f :=
  abelian_centered_exclusion G 11 133 101 2 9 5 9 1 0 ⟨(-1848),(-121),75,2⟩
    (fun r => [1848,242,132,0,0,528,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_133_1454 (hg : Fintype.card G=1463) : ¬ ∃ f : G → ℤ, IsSDS 1454 1355 f :=
  abelian_centered_exclusion G 11 133 1454 1355 9 128 9 1 0 ⟨(-133),1,0,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_139_104 (hg : Fintype.card G=1529) : ¬ ∃ f : G → ℤ, IsSDS 104 5 f :=
  abelian_centered_exclusion G 11 139 104 5 9 8 9 1 0 ⟨(-7388430),(-1583235),299871,107965⟩
    (fun r => [7388430,3166470,527745,0,0,2110980,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_139_1457 (hg : Fintype.card G=1529) : ¬ ∃ f : G → ℤ, IsSDS 1457 1358 f :=
  abelian_centered_exclusion G 11 139 1457 1358 9 131 9 1 0 ⟨(-139),1,0,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_167_100 (hg : Fintype.card G=1837) : ¬ ∃ f : G → ℤ, IsSDS 100 1 f :=
  abelian_centered_exclusion G 11 167 100 1 9 4 9 1 0 ⟨(-264),(-11),15,(-2)⟩
    (fun r => [264,22,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_695_100 (hg : Fintype.card G=7645) : ¬ ∃ f : G → ℤ, IsSDS 100 1 f :=
  abelian_centered_exclusion G 11 695 100 1 9 8 9 1 0 ⟨(-147467105597664),(-35435194540000),6621188290125,0⟩
    (fun r => [147467105597664,70873943262000,61532530948000,0,0,0,0,3893829362000,0,0,0].getD r 0) hg (by decide +kernel)

private theorem nine_11_695_7569 (hg : Fintype.card G=7645) : ¬ ∃ f : G → ℤ, IsSDS 7569 7470 f :=
  abelian_centered_exclusion G 11 695 7569 7470 9 687 9 1 0 ⟨(-695),1,0,0⟩
    (fun r => [0,0,0,0,0,0,0,0,0,0,0].getD r 0) hg (by decide +kernel)

theorem fixed_nine_11 {m : ℕ} {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f) (hG : Fintype.card G=11*m)
    (hm : 11 < m) (hn : k-lam=(11:ℤ)*9) : False := by
  have h := listed9 hf hG hm hn (by decide) (B:=901) (by intro t ht; omega) grid_11
  simp only [nineList,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 165 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=113 := by omega
    rw [hk,hL] at hf
    exact nine_11_19_113 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 231 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 231 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=162 := by omega
    rw [hk,hL] at hf
    exact nine_11_25_162 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=173 := by omega
    rw [hk,hL] at hf
    exact nine_11_25_173 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=100 := by omega
    rw [hk,hL] at hf
    exact nine_11_35_100 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=144 := by omega
    rw [hk,hL] at hf
    exact nine_11_35_144 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=265 := by omega
    rw [hk,hL] at hf
    exact nine_11_35_265 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 407 99 37 11 3 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 407 99 37 11 3 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=108 := by omega
    rw [hk,hL] at hf
    exact nine_11_43_108 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=449 := by omega
    rw [hk,hL] at hf
    exact nine_11_43_449 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 495 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 495 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 495 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=117 := by omega
    rw [hk,hL] at hf
    exact nine_11_49_117 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=458 := by omega
    rw [hk,hL] at hf
    exact nine_11_49_458 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 583 99 53 11 13 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 583 99 53 11 13 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 693 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 693 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 1419 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 1419 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=101 := by omega
    rw [hk,hL] at hf
    exact nine_11_133_101 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=1454 := by omega
    rw [hk,hL] at hf
    exact nine_11_133_1454 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=104 := by omega
    rw [hk,hL] at hf
    exact nine_11_139_104 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=1457 := by omega
    rw [hk,hL] at hf
    exact nine_11_139_1457 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 1617 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 1617 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=100 := by omega
    rw [hk,hL] at hf
    exact nine_11_167_100 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 2915 99 53 11 13 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 2915 99 53 11 13 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 4257 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 4257 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 4851 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    exact quotient_certificate_false hf hG (by simpa using hn) (by decide +kernel : quotientCertificate 4851 99 3 11 1 0 9)
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=100 := by omega
    rw [hk,hL] at hf
    exact nine_11_695_100 hG ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := h
    subst m
    have hk : k=7569 := by omega
    rw [hk,hL] at hf
    exact nine_11_695_7569 hG ⟨f,hf⟩

#print axioms fixed_nine_11

end Signed39.Contraction
