import SignedRowCorrelation
import SignedSplit
import SignedField

/-! When p divides both orders and divides the norm exactly once, a nontrivial cofactor exceeds p. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def displacement (u : H → ℤ) (t : H) : ℤ := energy u - corr u t

omit [DecidableEq H] in
theorem displacement_squares (u : H → ℤ) (t : H) :
    2*displacement u t = ∑ x : H, (u x - u (x+t))^2 := by
  have he : (∑ x : H, (u (x+t))^2) = energy u := sum_translate (fun x => (u x)^2) t
  calc
    _ = ∑ x : H, ((u x)^2+(u (x+t))^2-2*(u x*u (x+t))) := by
      rw [sum_sub_distrib,sum_add_distrib,← mul_sum,he]
      change 2*(energy u-corr u t) = energy u+energy u-2*corr u t
      ring
    _ = _ := by apply sum_congr rfl; intros; ring

omit [DecidableEq H] in
theorem displacement_sum (u : H → ℤ) : (∑ t : H, displacement u t) = variance u := by
  simp [displacement,variance,sum_sub_distrib,← mass_sq,mass]

omit [Fintype H] [DecidableEq H] in
def periods (u : H → ℤ) : AddSubgroup H where
  carrier := {t | ∀ x, u (x+t)=u x}
  zero_mem' := by simp
  add_mem' := by rintro a b ha hb x; rw [← add_assoc,hb,ha]
  neg_mem' := by rintro a ha x; simpa using (ha (x + -a)).symm

omit [DecidableEq H] in
theorem displacement_zero (u : H → ℤ) (t : H) :
    displacement u t = 0 ↔ t ∈ periods u := by
  constructor
  · intro hz x
    have h := displacement_squares u t
    rw [hz,mul_zero] at h
    have h0 := (sum_eq_zero_iff_of_nonneg (s:=univ)
      (fun x _ => sq_nonneg (u x-u (x+t)))).mp h.symm x (mem_univ x)
    nlinarith [sq_nonneg (u x-u (x+t)-1), sq_nonneg (u x-u (x+t)+1)]
  · intro ht
    have h (x : H) : u (x+t) = u x := ht x
    simp [displacement,energy,corr,h,pow_two]

omit [DecidableEq H] in
theorem period_card_dvd (u : H → ℤ) (t : H) :
    (Nat.card (periods u) : ℤ) ∣ displacement u t := by
  classical
  let L := periods u
  let m := QuotientAddGroup.mk' L
  let h := fun x => (u x)^2-u x*u (x+t)
  let r := fun q : H ⧸ L => h q.out
  have desc (x : H) : r (m x)=h x := by
    have eq : ((m x).out : H ⧸ L) = (x : H ⧸ L) := Quotient.out_eq' (m x)
    have member : -(m x).out+x ∈ L := QuotientAddGroup.eq.mp eq
    have e₁ := member (m x).out
    have e₂ := member ((m x).out+t)
    rw [show (m x).out+(-(m x).out+x) = x by abel] at e₁
    rw [show (m x).out+t+(-(m x).out+x) = x+t by abel] at e₂
    simp [r,h,e₁,e₂]
  let : Fintype (H ⧸ L) := Fintype.ofFinite _
  have fibers (z : H ⧸ L) : Nat.card {x // m x=z} = Nat.card L := by
    calc
      _ = Nat.card m.ker := Nat.card_congr
        (AddMonoidHom.fiberEquivKerOfSurjective (f:=m) (QuotientAddGroup.mk'_surjective L) z)
      _ = _ := by rw [show m.ker=L from QuotientAddGroup.ker_mk' L]
  have uniform := Signed39.FieldConstruction.uniform_sum m r (Nat.card L) fibers
  refine ⟨∑ q : H ⧸ L, r q,?_⟩
  rw [← uniform]
  simp only [desc,h,sum_sub_distrib,displacement,energy,corr]

theorem row_displacement_dvd {p : ℕ} [Fact p.Prime] {k lam s : ℤ} {f : ZMod p × H → ℤ}
    (hf : IsSDS k lam f) (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s)
    (hp : p.Coprime (Fintype.card H)) (i : ZMod p) (t : H) :
    (p:ℤ) ∣ displacement (row f i) t := by
  have h₁ := row_corr_dvd hf hn hp i 0
  have h₂ := row_corr_dvd hf hn hp i t
  have d := dvd_sub h₁ h₂
  rw [← energy_zero] at d
  have e : (p:ℤ) ∣ s*displacement (row f i) t := by
    convert d using 1
    dsimp [displacement]
    ring
  exact ((Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_or_dvd e).resolve_left hs

theorem cofactor_bound {p : ℕ} [Fact p.Prime] {k lam s : ℤ} {f : ZMod p × H → ℤ}
    (hf : IsSDS k lam f) (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s)
    (hp : p.Coprime (Fintype.card H)) (hm : 1 < Fintype.card H) :
    p < Fintype.card H := by
  classical
  by_contra! hlarge
  have hprime : Nat.Prime p := Fact.out
  have pne : (p:ℤ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have ppos : (0:ℤ) < p := by exact_mod_cast hprime.pos
  have hneq : k ≠ lam := by
    intro he
    rw [he,sub_self] at hn
    have := (mul_eq_zero.mp hn.symm).resolve_left pne
    exact hs (this ▸ dvd_zero _)
  obtain ⟨i,x,y,hxy⟩ := varying_row hf hneq (by omega)
  let u := row f i
  let m := Fintype.card H
  have hdiff : p ≠ m := by
    intro eq
    exact (hprime.coprime_iff_not_dvd.mp hp) (eq ▸ dvd_refl _)
  have hbig : (m:ℤ)+1 ≤ p := by change p ≠ Fintype.card H at hdiff; dsimp [m]; omega
  have hm' : 2 ≤ (m:ℤ) := by dsimp [m]; omega
  have ht (x : H) : u x = -1 ∨ u x=0 ∨ u x=1 := hf.ternary (i,x)
  have divides (t : H) : (p:ℤ) ∣ displacement u t := row_displacement_dvd hf hn hs hp i t
  have two (t : H) : displacement u t = 0 ∨ displacement u t = p := by
    have dp := displacement_squares u t
    have lower : 0 ≤ ∑ x : H, (u x-u (x+t))^2 := sum_nonneg (fun _ _ => sq_nonneg _)
    have le (x : H) : (u x-u (x+t))^2 ≤ 4 := by
      rcases ht x with a|a|a <;> rcases ht (x+t) with b|b|b <;> norm_num [a,b]
    have upper := sum_le_sum (s:=univ) (fun x _ => le x)
    simp only [sum_const,card_univ,nsmul_eq_mul] at upper
    change _ ≤ (m:ℤ)*4 at upper
    obtain ⟨q,hq⟩ := divides t
    have hlo : 0 ≤ q := by
      exact nonneg_of_mul_nonneg_right (show 0 ≤ (p:ℤ)*q by omega) ppos
    have hhi : q < 2 := by
      by_contra! h
      have h2 := mul_le_mul_of_nonneg_left h ppos.le
      omega
    rcases (show q=0 ∨ q=1 by omega) with h|h <;> simp [hq,h]
  have some_shift : ∃ t, displacement u t = p := by
    by_contra! none
    have d : displacement u (y-x)=0 := (two _).resolve_right (none _)
    have h := (displacement_zero u (y-x)).mp d x
    rw [show x+(y-x)=y by abel] at h
    exact hxy h.symm
  obtain ⟨t,ht'⟩ := some_shift
  let L := periods u
  have divides_p : Nat.card L ∣ p := by
    have h := period_card_dvd u t
    rw [ht'] at h
    exact_mod_cast h
  have divides_m : Nat.card L ∣ m := by
    simpa [m,← Nat.card_eq_fintype_card] using L.card_addSubgroup_dvd_card
  have size : Nat.card L = 1 := by
    have h := Nat.dvd_gcd divides_p divides_m
    change Nat.card L ∣ p.gcd (Fintype.card H) at h
    exact Nat.dvd_one.mp (hp.gcd_eq_one ▸ h)
  have : Subsingleton L := by
    have : Fintype L := Fintype.ofFinite L
    apply Fintype.card_le_one_iff_subsingleton.mp
    simp [← Nat.card_eq_fintype_card,size]
  have dt (w : H) : displacement u w = if w=0 then 0 else (p:ℤ) := by
    by_cases hw : w=0
    · subst w
      simp [displacement_zero]
    · simp only [ite_eq_right hw]
      apply (two w).resolve_left
      intro hz
      have hwL : w ∈ L := (displacement_zero u w).mp hz
      exact hw (congrArg Subtype.val (Subsingleton.elim (⟨w,hwL⟩ : L) 0))
  have sumdisp : (∑ w : H, displacement u w) = (p:ℤ)*((m:ℤ)-1) := by
    have d' (w : H) : displacement u w = (p:ℤ)-(if w=0 then (p:ℤ) else 0) := by
      rw [dt]; split_ifs <;> simp
    simp [d',sum_sub_distrib,m]
    ring
  rw [displacement_sum] at sumdisp
  have bound := variance_ternary u ht
  change variance u ≤ (m:ℤ)^2 at bound
  have peq : (p:ℤ)=(m:ℤ)+1 := by
    by_contra! hn
    have hmore : (m:ℤ)+2 ≤ p := by omega
    have hsub := mul_le_mul_of_nonneg_right hmore (show (0:ℤ)≤(m:ℤ)-1 by omega)
    have meq : (m:ℤ)=2 := by nlinarith
    rw [meq] at hsub hbig hmore sumdisp bound
    have p4 : p=4 := by omega
    exact (by decide : ¬ Nat.Prime 4) (p4 ▸ hprime)
  have hfull : energy u = (m:ℤ) := by
    have he : energy u ≤ (m:ℤ) := calc
      _ ≤ ∑ _ : H, (1:ℤ) := sum_le_sum (fun x _ => by rcases ht x with e|e|e <;> norm_num [e])
      _ = _ := by simp [m]
    by_contra! h
    have hs' : energy u ≤ (m:ℤ)-1 := by omega
    have hsub := mul_le_mul_of_nonneg_left hs' (show 0 ≤ (m:ℤ) by omega)
    change (m:ℤ)*energy u-(mass u)^2 = _ at sumdisp
    rw [peq] at sumdisp
    nlinarith [sq_nonneg (mass u)]
  have hap : 2 ∣ energy u-mass u := by
    change 2 ∣ (∑ x, u x^2)-∑ x, u x
    rw [← sum_sub_distrib]
    exact dvd_sum (fun x _ => by rcases ht x with e|e|e <;> norm_num [e])
  have hav : (mass u)^2=(1:ℤ)^2 := by
    change (m:ℤ)*energy u-(mass u)^2 = _ at sumdisp
    rw [peq,hfull] at sumdisp
    nlinarith
  obtain ⟨a,ha⟩ := hprime.odd_of_ne_two (show p≠2 by omega)
  rw [hfull] at hap
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hav with h|h <;> omega

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- A prime that divides the group order and the norm exactly once in the norm
also divides the group order exactly once. -/
theorem valuation_one_coprime {p m : ℕ} [Fact p.Prime] {k lam s : ℤ} {f : G → ℤ}
    (hf : IsSDS k lam f) (hg : Fintype.card G=p*m)
    (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s) : p.Coprime m := by
  have hprime : Nat.Prime p := Fact.out
  have hpr := Nat.prime_iff_prime_int.mp hprime
  exact hprime.coprime_iff_not_dvd.mpr (by
    rintro ⟨t,ht⟩
    have he := sds_mass hf
    rw [hn,hg,ht,Nat.cast_mul,Nat.cast_mul] at he
    have d : (p:ℤ) ∣ (mass f)^2 := ⟨s+(p:ℤ)*t*lam,by rw [he]; ring⟩
    obtain ⟨z,hz⟩ := hpr.dvd_of_dvd_pow d
    apply hs
    refine ⟨z^2-(t:ℤ)*lam,?_⟩
    apply mul_left_cancel₀ hpr.ne_zero
    rw [hz] at he
    linear_combination -he)

/-- An arbitrary abelian group of order pm with m>1 requires p<m whenever p divides the norm exactly once. -/
theorem abelian_cofactor_bound {p m : ℕ} [Fact p.Prime] {k lam s : ℤ} {f : G → ℤ}
    (hf : IsSDS k lam f) (hg : Fintype.card G=p*m) (hm : 1 < m)
    (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s) : p < m := by
  classical
  have cp := valuation_one_coprime hf hg hn hs
  obtain ⟨K,hK,⟨e⟩⟩ := split_prime_factor hg cp
  have size : Fintype.card (Additive K) = m := Nat.card_eq_fintype_card.symm.trans hK
  exact size ▸ cofactor_bound (pullback hf e) hn hs (size ▸ cp) (size ▸ hm)

theorem cofactor_exclusion (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p m : ℕ) (k lam s : ℤ) (hg : Fintype.card G=p*m)
    (h : p.Prime ∧ 1 < m ∧ m ≤ p ∧ k-lam=(p:ℤ)*s ∧ ¬ (p:ℤ) ∣ s) :
    ¬ ∃ f : G → ℤ, IsSDS k lam f := by
  rintro ⟨f,hf⟩
  have : Fact p.Prime := ⟨h.1⟩
  exact h.2.2.1.not_gt (abelian_cofactor_bound hf hg h.2.1 h.2.2.2.1 h.2.2.2.2)

#print axioms abelian_cofactor_bound

end Signed39.Contraction
