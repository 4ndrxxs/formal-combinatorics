import SignedMoments
import SignedSplit

/-! A finite separating inequality excludes a parameter set when every admissible row
obeys the inequality and the required total moments violate its sum. -/

namespace Signed39.Contraction

open Finset

structure Separator where
  constant : ℤ
  linear : ℤ
  weight : ℤ
  square : ℤ
  deriving DecidableEq

def Separator.value (h : Separator) (j a b q : ℤ) : ℤ :=
  h.constant*j+h.linear*a+h.weight*b+h.square*q

def rowCertificate (p m : ℕ) (k lam s c : ℤ) (h : Separator) : Prop :=
  p.Prime ∧ p.Coprime m ∧ k-lam=(p:ℤ)*s ∧
  ((p:ℤ)*c)^2=k-lam+((p:ℤ)*m)*lam ∧
  h.value p ((p:ℤ)*c) k (k-lam+(m:ℤ)*lam) < 0 ∧
  ∀ u : Fin (2*m+1), ∀ w : Fin (m+1),
    let a := (u.val:ℤ) - (m:ℤ)
    let b := (w.val:ℤ)
    admissibleRow p m s lam c a b → 0 ≤ h.value 1 a b (a^2)

instance (p m : ℕ) (k lam s c : ℤ) (h : Separator) : Decidable (rowCertificate p m k lam s c h) := by
  unfold rowCertificate
  infer_instance

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {p : ℕ} [Fact p.Prime]

theorem row_family_exclusion {k lam s c : ℤ} {m : ℕ} {h : Separator} {P : ℤ → ℤ → Prop}
    (hm : Fintype.card H=m) (hcop : p.Coprime m) (hn : k-lam=(p:ℤ)*s)
    (hc2 : ((p:ℤ)*c)^2=k-lam+((p:ℤ)*m)*lam)
    (hbad : h.value p ((p:ℤ)*c) k (k-lam+(m:ℤ)*lam) < 0)
    (hall : ∀ u : Fin (2*m+1), ∀ w : Fin (m+1),
      let a := (u.val:ℤ)-(m:ℤ)
      let b := (w.val:ℤ)
      admissibleRow p m s lam c a b → P a b → 0 ≤ h.value 1 a b (a^2))
    (rows : ∀ {f : ZMod p × H → ℤ}, IsSDS k lam f → ∀ i, P (mass (row f i)) (energy (row f i))) :
    ¬ ∃ f : ZMod p × H → ℤ, IsSDS k lam f := by
  rintro ⟨g,hg⟩
  have hmass := sds_mass hg
  rw [Fintype.card_prod,ZMod.card,hm,Nat.cast_mul,← hc2] at hmass
  obtain ⟨f,hf,hmain⟩ : ∃ f : ZMod p × H → ℤ, IsSDS k lam f ∧ mass f=(p:ℤ)*c := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hmass with h|h
    · exact ⟨g,hg,h⟩
    · exact ⟨fun x => -g x,hg.neg,by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using h⟩
  let a := fun i => mass (row f i)
  let b := fun i => energy (row f i)
  have row_ok (i : ZMod p) : 0 ≤ h.value 1 (a i) (b i) ((a i)^2) := by
    have hh := row_admissible hf hn hmain (hm ▸ hcop) i
    rw [hm] at hh
    change admissibleRow p m s lam c (a i) (b i) at hh
    have bounds := hh
    obtain ⟨h1,h2,h3,h4,_,_,_⟩ := bounds
    let u : Fin (2*m+1) := ⟨(a i+m).toNat,by omega⟩
    let w : Fin (m+1) := ⟨(b i).toNat,by omega⟩
    have hu : (u.val:ℤ)-(m:ℤ)=a i := by dsimp [u]; omega
    have hw : (w.val:ℤ)=b i := by dsimp [w]; omega
    simpa only [hu,hw] using hall u w (by simpa only [hu,hw] using hh)
      (by simpa only [hu,hw] using rows hf i)
  have sum_a : (∑ i, a i)=(p:ℤ)*c := (mass_rowmass f).trans hmain
  have sum_b : (∑ i, b i)=k := by
    simpa [b,energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  have sum_aa : (∑ i, (a i)^2)=k-lam+(m:ℤ)*lam := by
    change energy (rowMass f) = _
    simpa only [← energy_zero,ite_true,hm] using rowmass_corr hf 0
  have sum_ok := sum_nonneg (s := univ) (fun i _ => row_ok i)
  simp only [Separator.value,mul_one,sum_add_distrib,sum_const,card_univ,ZMod.card,
    nsmul_eq_mul, ← mul_sum,sum_a,sum_b,sum_aa] at sum_ok
  unfold Separator.value at hbad
  linarith only [sum_ok,hbad]

theorem row_certificate_false {k lam s c : ℤ} {m : ℕ} {h : Separator}
    (hc : rowCertificate p m k lam s c h) (hm : Fintype.card H=m) :
    ¬ ∃ f : ZMod p × H → ℤ, IsSDS k lam f := by
  obtain ⟨_,hcop,hn,hc2,hbad,hall⟩ := hc
  exact row_family_exclusion (P := fun _ _ => True) hm hcop hn hc2 hbad
    (fun u w hw _ => hall u w hw) (fun _ _ => trivial)

theorem abelian_row_exclusion (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p m : ℕ) (k lam s c : ℤ) (h : Separator) (hg : Fintype.card G=p*m)
    (hv : rowCertificate p m k lam s c h) : ¬ ∃ f : G → ℤ, IsSDS k lam f := by
  classical
  have : Fact p.Prime := ⟨hv.1⟩
  obtain ⟨K,hK,⟨e⟩⟩ := split_prime_factor hg hv.2.1
  rintro ⟨f,hf⟩
  have hc : Fintype.card (Additive K)=m := Nat.card_eq_fintype_card.symm.trans hK
  exact row_certificate_false hv hc ⟨_,pullback hf e⟩

#print axioms abelian_row_exclusion

end Signed39.Contraction
