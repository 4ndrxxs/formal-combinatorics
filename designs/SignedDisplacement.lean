import SignedCofactor
import SignedMomentCertificate

/-! Integral displacement bounds determined by the signed mass and weight of one row. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def rowLimit (m a b : ℤ) : ℤ := min (2*b-|a|) (m+b-2*|a|)

omit [DecidableEq H] in
theorem displacement_upper (u : H → ℤ) (ht : ∀ x, u x= -1 ∨ u x=0 ∨ u x=1) (t : H) :
    displacement u t ≤ rowLimit (Fintype.card H) (mass u) (energy u) := by
  obtain ⟨e,he,hab⟩ : ∃ e : ℤ, (e=1 ∨ e= -1) ∧ |mass u|=e*mass u := by
    by_cases h : 0 ≤ mass u
    · exact ⟨1,Or.inl rfl,by simp [abs_of_nonneg h]⟩
    · exact ⟨-1,Or.inr rfl,by simp [abs_of_neg (lt_of_not_ge h)]⟩
  have bounds (x : H) :
      (u x-u (x+t))^2 ≤ 2*(u x)^2+2*(u (x+t))^2-e*u x-e*u (x+t) ∧
      (u x-u (x+t))^2 ≤ 2+(u x)^2+(u (x+t))^2-2*e*u x-2*e*u (x+t) := by
    rcases he with a|a <;> rcases ht x with b|b|b <;> rcases ht (x+t) with c|c|c <;> norm_num [a,b,c]
  have h₁ := sum_le_sum (s:=univ) (fun x _ => (bounds x).1)
  have h₂ := sum_le_sum (s:=univ) (fun x _ => (bounds x).2)
  have hE : (∑ x : H, (u (x+t))^2) = energy u := sum_translate (fun x => (u x)^2) t
  have hA : (∑ x : H, u (x+t)) = mass u := sum_translate u t
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,hE,hA,sum_const,card_univ,nsmul_eq_mul,
    ← displacement_squares] at h₁ h₂
  change _ ≤ 2*energy u+2*energy u-e*mass u-e*mass u at h₁
  change _ ≤ (Fintype.card H:ℤ)*2+energy u+energy u-2*e*mass u-2*e*mass u at h₂
  rw [rowLimit,hab]
  exact le_min (by linarith) (by linarith)

omit [DecidableEq H] in
theorem displacement_nonneg (u : H → ℤ) (t : H) : 0 ≤ displacement u t := by
  have h := displacement_squares u t
  have h0 : 0 ≤ ∑ x : H, (u x-u (x+t))^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  omega

omit [DecidableEq H] in
theorem variation_lower {p : ℕ} (u : H → ℤ) (cp : p.Coprime (Fintype.card H))
    (hd : ∀ t, (p:ℤ) ∣ displacement u t) {x y : H} (hxy : u x ≠ u y) :
    (p:ℤ)*((Fintype.card H:ℤ)-1) ≤ variance u := by
  classical
  let L := periods u
  let l := Nat.card L
  let m := Fintype.card H
  have hl : 0 < l := Nat.card_pos
  have lsize : (univ.filter (fun t : H => t ∈ L)).card = l := by
    rw [← Fintype.card_subtype]
    exact Nat.card_eq_fintype_card.symm
  have proper : y-x ∉ L := by
    intro h
    have e := h x
    rw [show x+(y-x)=y by abel] at e
    exact hxy e.symm
  have small : l < m := by
    rw [← lsize]
    apply card_lt_univ_of_notMem (x:=y-x)
    simp [proper]
  have dv : l ∣ m := by simpa [l,m,← Nat.card_eq_fintype_card] using L.card_addSubgroup_dvd_card
  have cop : IsCoprime (p:ℤ) (l:ℤ) := (Nat.Coprime.of_dvd_right dv cp).isCoprime
  let weight := (p:ℤ)*(l:ℤ)
  have each (t : H) : weight-(if t∈L then weight else 0) ≤ displacement u t := by
    by_cases h : t∈L
    · simpa [h] using displacement_nonneg u t
    · simp only [ite_eq_right h,sub_zero]
      have d := cop.mul_dvd (hd t) (period_card_dvd u t)
      have pos := (displacement_nonneg u t).lt_of_ne (fun e => h ((displacement_zero u t).mp e.symm))
      exact Int.le_of_dvd pos d
  have lower := sum_le_sum (s:=univ) (fun t _ => each t)
  have cnt : (∑ t : H, if t∈L then weight else 0) = (l:ℤ)*weight := by simp [sum_ite,lsize]
  rw [sum_sub_distrib,cnt,sum_const,card_univ,displacement_sum,nsmul_eq_mul] at lower
  change (m:ℤ)*((p:ℤ)*l)-(l:ℤ)*((p:ℤ)*l) ≤ variance u at lower
  have hl' : (0:ℤ) ≤ (l:ℤ)-1 := by omega
  have hm' : (0:ℤ) ≤ (m:ℤ)-(l:ℤ)-1 := by omega
  have prod := mul_nonneg (Nat.cast_nonneg p : 0 ≤ (p:ℤ)) (mul_nonneg hl' hm')
  change (p:ℤ)*((m:ℤ)-1) ≤ variance u
  nlinarith

theorem variation_upper {p : ℕ} (hp : 0 < p) (u : H → ℤ) (ht : ∀ x, u x= -1 ∨ u x=0 ∨ u x=1)
    (hd : ∀ t, (p:ℤ) ∣ displacement u t) :
    variance u ≤ (rowLimit (Fintype.card H) (mass u) (energy u)/(p:ℤ))*(p:ℤ)*((Fintype.card H:ℤ)-1) := by
  let lim := rowLimit (Fintype.card H) (mass u) (energy u)
  let bound := (lim/(p:ℤ))*(p:ℤ)
  have hp' : 0 < (p:ℤ) := by exact_mod_cast hp
  have each (t : H) : displacement u t ≤ bound-(if t=0 then bound else 0) := by
    by_cases h0 : t=0
    · subst t; simp [displacement,← energy_zero]
    · simp only [ite_eq_right h0,sub_zero]
      obtain ⟨z,hz⟩ := hd t
      have h := displacement_upper u ht t
      change _ ≤ lim at h
      rw [hz,mul_comm] at h
      have le := (Int.le_ediv_iff_mul_le hp').mpr h
      have b := mul_le_mul_of_nonneg_right le hp'.le
      simpa only [hz,mul_comm (p:ℤ),bound] using b
  have h := sum_le_sum (s:=univ) (fun t _ => each t)
  simp only [displacement_sum,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,
    sum_ite_eq',mem_univ,ite_true] at h
  change variance u ≤ bound*((Fintype.card H:ℤ)-1)
  linarith

def admissibleShift (p m a b : ℤ) : Prop :=
  m*b-a^2 = 0 ∨
  p*(m-1) ≤ m*b-a^2 ∧ m*b-a^2 ≤ (rowLimit m a b/p)*p*(m-1)

instance (p m a b : ℤ) : Decidable (admissibleShift p m a b) := by
  unfold admissibleShift
  infer_instance

theorem row_shift_admissible {p : ℕ} [Fact p.Prime] {k lam s : ℤ} {f : ZMod p × H → ℤ}
    (hf : IsSDS k lam f) (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s)
    (hp : p.Coprime (Fintype.card H)) (i : ZMod p) :
    admissibleShift p (Fintype.card H) (mass (row f i)) (energy (row f i)) := by
  classical
  let u := row f i
  have d := row_displacement_dvd hf hn hs hp i
  by_cases h : ∃ x y : H, u x ≠ u y
  · obtain ⟨x,y,hxy⟩ := h
    exact Or.inr ⟨variation_lower u hp d hxy,
      variation_upper (Fact.out : p.Prime).pos u (fun z => hf.ternary (i,z)) d⟩
  · push Not at h
    exact Or.inl (variance_constant u (u 0) (fun z => h z 0))

def shiftCertificate (p m : ℕ) (k lam s c : ℤ) (h : Separator) : Prop :=
  p.Prime ∧ p.Coprime m ∧ k-lam=(p:ℤ)*s ∧ ¬ (p:ℤ) ∣ s ∧
  ((p:ℤ)*c)^2=k-lam+((p:ℤ)*m)*lam ∧
  h.value p ((p:ℤ)*c) k (k-lam+(m:ℤ)*lam) < 0 ∧
  ∀ u : Fin (2*m+1), ∀ w : Fin (m+1),
    let a := (u.val:ℤ)-(m:ℤ)
    let b := (w.val:ℤ)
    admissibleRow p m s lam c a b → admissibleShift p m a b → 0 ≤ h.value 1 a b (a^2)

instance (p m : ℕ) (k lam s c : ℤ) (h : Separator) : Decidable (shiftCertificate p m k lam s c h) := by
  unfold shiftCertificate
  infer_instance

theorem abelian_shift_exclusion (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p m : ℕ) (k lam s c : ℤ) (h : Separator) (hg : Fintype.card G=p*m)
    (hv : shiftCertificate p m k lam s c h) : ¬ ∃ f : G → ℤ, IsSDS k lam f := by
  classical
  obtain ⟨hp,hcop,hn,hs,hc2,hbad,hall⟩ := hv
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K,hK,⟨e⟩⟩ := split_prime_factor hg hcop
  rintro ⟨f,hf⟩
  have hm : Fintype.card (Additive K) = m := Nat.card_eq_fintype_card.symm.trans hK
  apply row_family_exclusion (P:=admissibleShift p m) hm hcop hn hc2 hbad hall _ ⟨_,pullback hf e⟩
  intro g h i
  simpa only [hm] using row_shift_admissible h hn hs (hm ▸ hcop) i

#print axioms abelian_shift_exclusion

end Signed39.Contraction
