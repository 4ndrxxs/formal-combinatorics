import SignedMoments

/-! Every shift of each row satisfies a congruence obtained from its integral contraction. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {p : ℕ} [Fact p.Prime]

theorem matched_corr (a s : H → ℤ) (n l : ℤ)
    (hh : ∀ t, corr s t = (if t=0 then n else 0)+l) (t : H) :
    corr (matched a s) t = n*corr a t + l*(mass a)^2 := by
  have inner (x y : H) : (∑ z : H, s (x-z)*s (y-(z+t))) = corr s (y-(x+t)) := by
    apply Fintype.sum_equiv (Equiv.subLeft x)
    intro z
    change s (x-z)*s (y-(z+t)) = s (x-z)*s ((x-z)+(y-(x+t)))
    rw [show (x-z)+(y-(x+t)) = y-(z+t) by abel]
  calc
    _ = ∑ z : H, ∑ x : H, ∑ y : H, a x*a y*(s (x-z)*s (y-(z+t))) := by
      simp only [corr,matched,sum_mul,mul_sum]
      apply sum_congr rfl; intro z _
      rw [sum_comm]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intros
      ring
    _ = ∑ x : H, ∑ y : H, ∑ z : H, a x*a y*(s (x-z)*s (y-(z+t))) := by
      rw [sum_comm]
      apply sum_congr rfl; intro x _
      rw [sum_comm]
    _ = ∑ x : H, ∑ y : H, ((if y=x+t then n*(a x*a (x+t)) else 0) + l*(a x*a y)) := by
      simp only [← mul_sum,inner,hh]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro y _
      by_cases h : y=x+t <;> simp [h,sub_eq_zero] <;> ring
    _ = _ := by simp [sum_add_distrib, ← mul_sum, ← sum_mul,corr,mass,pow_two]

theorem row_corr_dvd {k lam s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*s) (hc : p.Coprime (Fintype.card H)) (i : ZMod p) (t : H) :
    (p:ℤ) ∣ s*corr (row f i) t+lam*(mass (row f i))^2 := by
  choose w hw using matched_dvd hf ⟨s,hn⟩ hc i
  have hid : matched (row f i) (fiber f) = fun z => (p:ℤ)*w z := funext hw
  have h := matched_corr (row f i) (fiber f) (k-lam) ((Fintype.card (ZMod p):ℤ)*lam) (fiber_flat hf) t
  rw [hid,ZMod.card,hn] at h
  have hscale : corr (fun x => (p:ℤ)*w x) t = (p:ℤ)^2*corr w t := by
    simp only [corr,mul_sum]
    apply sum_congr rfl; intros
    ring
  rw [hscale] at h
  refine ⟨corr w t,?_⟩
  apply mul_left_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p:ℤ) ≠ 0)
  linear_combination -h

#print axioms row_corr_dvd

end Signed39.Contraction
