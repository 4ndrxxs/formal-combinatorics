import SignedBasic

/-! A product construction for signed difference sets. The first factor supplies
a difference set and a weighing sequence on its complement. The second factor
supplies a balanced ternary sequence with nonzero autocorrelations `-1`. -/

namespace Signed39.Product

open Finset

variable {U V : Type} [AddCommGroup U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

def combine (s w : U → ℤ) (l : V → ℤ) (x : U × V) : ℤ := s x.1 + w x.1 * l x.2

omit [DecidableEq U] [DecidableEq V] in
theorem combined_corr (s w : U → ℤ) (l : V → ℤ) (hl : ∑ j : V, l j = 0) (a : U) (b : V) :
    corr (combine s w l) (a,b) = (Fintype.card V:ℤ) * corr s a + corr w a * corr l b := by
  have htl : (∑ j : V, l (j+b)) = 0 :=
    (Fintype.sum_equiv (Equiv.addRight b) _ _ (fun _ => rfl)).trans hl
  have inner (i : U) :
      (∑ j : V, (s i+w i*l j) * (s (i+a)+w (i+a)*l (j+b))) =
      (Fintype.card V:ℤ) * (s i*s (i+a)) + (w i*w (i+a))*corr l b := by
    calc
      _ = ∑ j : V, (s i*s (i+a) + (s i*w (i+a))*l (j+b) +
          (w i*s (i+a))*l j + (w i*w (i+a))*(l j*l (j+b))) := by
            apply sum_congr rfl
            intros
            ring
      _ = _ := by simp [sum_add_distrib, ← mul_sum, hl, htl, corr]
  simp only [corr, Fintype.sum_prod_type, combine, Prod.mk_add_mk, inner,
    sum_add_distrib, ← mul_sum, ← sum_mul]

theorem product_sds (s w : U → ℤ) (l : V → ℤ) (r d : ℤ)
    (hwds : ∀ i, (s i = 1 ∧ w i = 0) ∨ (s i = 0 ∧ (w i = -1 ∨ w i = 1)))
    (hlv : ∀ j, l j = -1 ∨ l j = 0 ∨ l j = 1) (hl : ∑ j : V, l j = 0)
    (hs : ∀ a, corr s a = (if a = 0 then r else 0) + d)
    (hw : ∀ a, corr w a = if a = 0 then (Fintype.card V:ℤ)*r else 0)
    (hχ : ∀ b, corr l b = (if b = 0 then (Fintype.card V:ℤ) else 0) - 1) :
    IsSDS ((Fintype.card V:ℤ)^2*r + (Fintype.card V:ℤ)*d)
      ((Fintype.card V:ℤ)*d) (combine s w l) := by
  constructor
  · rintro ⟨i,j⟩
    rcases hwds i with ⟨hs',hw'⟩ | ⟨hs',hw' | hw'⟩ <;>
      rcases hlv j with hj | hj | hj <;> simp [combine, hs', hw', hj]
  · rintro ⟨a,b⟩
    rw [combined_corr _ _ _ hl, hs, hw, hχ]
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb, Prod.ext_iff] <;> ring

#print axioms product_sds

end Signed39.Product
