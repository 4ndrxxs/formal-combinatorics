import SignedFixedNormParameters
import SignedCapacityCases

/-! Complete fixed-norm obstructions at 21 and 56, including groups above the published table. -/

namespace Signed39.Contraction

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem fixed_21_false {k lam : ℤ} {m : ℕ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hG : Fintype.card G=3*m) (hm : 3 < m) (hn : k-lam=21) : False := by
  have num : k-lam=(3:ℤ)*(7:ℕ) := by omega
  obtain ⟨c,hp,hl,upper⟩ := bounded_parameters hf hG num (by decide : ¬ 3 ∣ 7) hm
  have lower := hp.1
  have odd := hp.2.1
  have cop := hp.2.2.1
  have cm := hp.2.2.2.1
  have bound : m<155 := by norm_num at upper; omega
  have valid := norm21_parameters ⟨m,bound⟩ lower odd cop ⟨c,by omega⟩
  change numericalParameter 3 m 7 c ((3*(c:ℤ)^2-7)/(m:ℤ)) → _ at valid
  norm_num at hl
  rw [← hl] at valid
  have remaining : list21 m := valid hp
  rcases remaining with h|h|h|h|h|h|h
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 21 21 7 3 3 0 7)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 51 21 17 3 8 0 7)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 75 21 5 3 2 0 7)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 105 21 5 3 2 0 7)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 111 21 37 3 9 0 7)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 123 21 41 3 4 0 7)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 303 21 101 3 50 0 7)

theorem fixed_56_false {k lam : ℤ} {m : ℕ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hG : Fintype.card G=7*m) (hm : 7 < m) (hn : k-lam=56) : False := by
  have num : k-lam=(7:ℤ)*(8:ℕ) := by omega
  obtain ⟨c,hp,hl,upper⟩ := bounded_parameters hf hG num (by decide : ¬ 7 ∣ 8) hm
  have lower := hp.1
  have odd := hp.2.1
  have cop := hp.2.2.1
  have cm := hp.2.2.2.1
  have bound : m<457 := by norm_num at upper; omega
  have valid := norm56_parameters ⟨m,bound⟩ lower odd cop ⟨c,by omega⟩
  change numericalParameter 7 m 8 c ((7*(c:ℤ)^2-8)/(m:ℤ)) → _ at valid
  norm_num at hl
  rw [← hl] at valid
  have remaining : list56 m lam := valid hp
  rcases remaining with h|h|h|h|h|h|h|h|h|h
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 77 56 11 7 5 0 8)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 91 56 13 7 6 0 8)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 175 56 5 7 2 0 8)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 301 56 43 7 3 0 8)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 385 56 5 7 2 0 8)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 427 56 61 7 30 0 8)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 469 56 67 7 33 0 8)
  · subst m
    exact quotient_certificate_false hf hG hn (by decide +kernel : quotientCertificate 2345 56 5 7 2 0 8)
  · obtain ⟨hM,hL|hL⟩ := h
    · subst m
      have hk : k=100 := by omega
      rw [hk,hL] at hf
      exact Signed39.CapacityCases.no_N11598 G hG ⟨f,hf⟩
    · subst m
      have hk : k=121 := by omega
      rw [hk,hL] at hf
      exact Signed39.CapacityCases.no_N11607 G hG ⟨f,hf⟩
  · obtain ⟨hM,hL|hL⟩ := h
    · subst m
      have hk : k=57 := by omega
      rw [hk,hL] at hf
      exact Signed39.CapacityCases.no_1169_57_1 G hG ⟨f,hf⟩
    · subst m
      have hk : k=1156 := by omega
      rw [hk,hL] at hf
      exact Signed39.CapacityCases.no_1169_1156_1100 G hG ⟨f,hf⟩

#print axioms fixed_21_false
#print axioms fixed_56_false

end Signed39.Contraction
