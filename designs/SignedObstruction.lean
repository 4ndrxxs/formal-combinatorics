import SignedContraction
import SignedVariance

/-! A necessary inequality for a signed difference set with a prime common to its order and its group. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {P : Type} [AddCommGroup P] [Fintype P] [DecidableEq P]
variable {p : ℕ} [Fact p.Prime]

omit [DecidableEq H] [DecidableEq P] in
theorem fiber_corr (f : P × H → ℤ) (t : H) :
    corr (fiber f) t = ∑ u : P, corr f (u,t) := by
  calc
    _ = ∑ y : H, ∑ i : P, ∑ j : P, f (i,y)*f (j,y+t) := by
      simp only [corr,fiber,sum_mul,mul_sum]
      apply sum_congr rfl
      intro y _
      rw [sum_comm]
    _ = ∑ i : P, ∑ u : P, ∑ y : H, f (i,y)*f (i+u,y+t) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
      symm
      exact Fintype.sum_equiv (Equiv.addLeft i) _ _ (fun _ => rfl)
    _ = _ := by rw [sum_comm]; simp only [corr,Fintype.sum_prod_type,Prod.mk_add_mk]

theorem fiber_flat {k lam : ℤ} {f : P × H → ℤ} (hf : IsSDS k lam f) (t : H) :
    corr (fiber f) t = (if t=0 then k-lam else 0) + (Fintype.card P:ℤ)*lam := by
  rw [fiber_corr]
  have hh (u : P) : corr f (u,t) =
      (if u=0 ∧ t=0 then k-lam else 0) + lam := by
    rw [hf.flat]
    by_cases h : u=0 ∧ t=0 <;> simp [Prod.ext_iff,h]
  simp_rw [hh]
  by_cases h : t=0 <;> simp [h,sum_add_distrib]

theorem mass_from_flat (s : H → ℤ) (n l : ℤ)
    (hf : ∀ t, corr s t = (if t=0 then n else 0) + l) :
    (mass s)^2 = n+(Fintype.card H:ℤ)*l := by
  have h := mass_sq s
  simp_rw [hf] at h
  simpa [mass,sum_add_distrib] using h

omit [DecidableEq H] in
theorem matched_mass (a s : H → ℤ) : mass (matched a s) = mass a*mass s := by
  have hs (x : H) : (∑ z : H, s (x-z))=mass s :=
    Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ => rfl)
  unfold mass matched
  rw [sum_comm]
  simp only [← mul_sum, hs, ← sum_mul]
  rfl

theorem matched_energy (a s : H → ℤ) (n l : ℤ)
    (hf : ∀ t, corr s t = (if t=0 then n else 0) + l) :
    energy (matched a s) = n*energy a + l*(mass a)^2 := by
  have inner (x y : H) : (∑ z : H, s (x-z)*s (y-z)) = corr s (y-x) := by
    apply Fintype.sum_equiv (Equiv.subLeft x)
    intro z
    change s (x-z)*s (y-z) = s (x-z)*s ((x-z)+(y-x))
    rw [show (x-z)+(y-x) = y-z by abel]
  calc
    _ = ∑ z : H, ∑ x : H, ∑ y : H, a x*a y*(s (x-z)*s (y-z)) := by
      simp only [energy,matched,pow_two,sum_mul,mul_sum]
      apply sum_congr rfl; intro z _
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intros
      ring
    _ = ∑ x : H, ∑ y : H, ∑ z : H, a x*a y*(s (x-z)*s (y-z)) := by
      rw [sum_comm]
      apply sum_congr rfl; intro x _
      rw [sum_comm]
    _ = ∑ x : H, ∑ y : H, ((if y=x then n*(a x)^2 else 0) + l*(a x*a y)) := by
      simp only [← mul_sum, inner, hf]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro y _
      by_cases h : y=x <;> simp [h,sub_eq_zero] <;> ring
    _ = _ := by simp [sum_add_distrib, ← mul_sum, ← sum_mul,energy,mass,pow_two]

theorem matched_variance (a s : H → ℤ) (n l : ℤ)
    (hf : ∀ t, corr s t = (if t=0 then n else 0) + l) :
    variance (matched a s) = n*variance a := by
  rw [variance,matched_energy a s n l hf,matched_mass,mul_pow,mass_from_flat s n l hf,variance]
  ring

theorem varying_row {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k ≠ lam) (hH : 1 < Fintype.card H) :
    ∃ i : ZMod p, ∃ x y : H, f (i,x) ≠ f (i,y) := by
  by_contra! h
  obtain ⟨x,y,hxy⟩ := Fintype.one_lt_card_iff.mp hH
  have hnz : ((0:ZMod p),x-y) ≠ (0:ZMod p × H) := fun he =>
    hxy (sub_eq_zero.mp (congrArg Prod.snd he))
  have hcor : corr f (0,x-y) = corr f 0 := by
    apply sum_congr rfl
    rintro ⟨i,u⟩ _
    simp only [Prod.mk_add_mk,add_zero]
    rw [h i (u+(x-y)) u]
  rw [hf.flat, hf.flat, ite_eq_right hnz, ite_eq_left rfl] at hcor
  exact hn hcor.symm

/-- Dividing the correlation with the projected word by p produces an integral
vector with prescribed variance. -/
theorem row_scale {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hp : (p:ℤ) ∣ k-lam) (hc : p.Coprime (Fintype.card H)) (i : ZMod p) :
    ∃ b : H → ℤ, (p:ℤ)^2*variance b = (k-lam)*variance (fun x => f (i,x)) := by
  choose b hb using (matched_dvd hf hp hc i)
  have hident : matched (fun x => f (i,x)) (fiber f) = fun z => (p:ℤ)*b z := funext hb
  have hv := matched_variance (fun x => f (i,x)) (fiber f) (k-lam)
    ((Fintype.card (ZMod p):ℤ)*lam) (fiber_flat hf)
  rw [hident,variance_scale] at hv
  exact ⟨b,hv⟩

/-- For n=k−λ divisible by p and G=C_p × H with p coprime to m=|H|>1,
a signed difference set requires p²(m−1)≤n m². -/
theorem prime_factor_bound {k lam : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : 0 < k-lam) (hp : (p:ℤ) ∣ k-lam) (hc : p.Coprime (Fintype.card H))
    (hH : 1 < Fintype.card H) :
    (p:ℤ)^2*((Fintype.card H:ℤ)-1) ≤ (k-lam)*(Fintype.card H:ℤ)^2 := by
  obtain ⟨i,x,y,hxy⟩ := varying_row hf (by omega) hH
  let a := fun z : H => f (i,z)
  obtain ⟨b,hv⟩ := row_scale hf hp hc i
  have ha := variance_minimum a hxy
  have ha' : 0 < variance a := by omega
  have hpos : 0 < variance b := by
    by_contra! h
    have hneg := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (p:ℤ)) h
    rw [hv] at hneg
    exact (not_lt_of_ge hneg) (mul_pos hn ha')
  obtain ⟨r,s,hrs⟩ : ∃ r s : H, b r ≠ b s := by
    by_contra! h
    exact hpos.ne' (variance_constant b (b 0) (fun r => h r 0))
  calc
    _ ≤ (p:ℤ)^2*variance b := mul_le_mul_of_nonneg_left (variance_minimum b hrs) (sq_nonneg _)
    _ = (k-lam)*variance a := hv
    _ ≤ _ := mul_le_mul_of_nonneg_left (variance_ternary a (fun z => hf.ternary (i,z))) hn.le

#print axioms prime_factor_bound

end Signed39.Contraction
