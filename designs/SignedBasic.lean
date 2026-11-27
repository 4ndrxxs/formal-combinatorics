import Mathlib

/-! Signed difference sets, their support size and elementary symmetries. -/

namespace Signed39

open Finset

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

def corr (f : G → ℤ) (t : G) : ℤ := ∑ x : G, f x * f (x + t)

structure IsSDS (k lam : ℤ) (f : G → ℤ) : Prop where
  ternary : ∀ x, f x = -1 ∨ f x = 0 ∨ f x = 1
  flat : ∀ t : G, corr f t = if t = 0 then k else lam

theorem support_card {k lam : ℤ} {f : G → ℤ} (h : IsSDS k lam f) :
    ((univ.filter (fun x => f x ≠ 0)).card : ℤ) = k := by
  rw [← show corr f 0 = k by simpa using h.flat 0, corr]
  simp only [add_zero]
  rw [← sum_boole]
  apply sum_congr rfl
  intro x _
  rcases h.ternary x with hx | hx | hx <;> simp [hx]

omit [DecidableEq G] in
theorem sum_translate (f : G → ℤ) (a : G) : (∑ x : G, f (x+a)) = ∑ x : G, f x :=
  Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

omit [DecidableEq G] in
theorem mass_sq (f : G → ℤ) : (∑ x : G, f x)^2 = ∑ t : G, corr f t := by
  rw [pow_two, Finset.sum_mul]
  simp only [corr]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  congr 1
  simpa [add_comm] using (sum_translate f x).symm

theorem IsSDS.neg {k lam : ℤ} {f : G → ℤ} (h : IsSDS k lam f) :
    IsSDS k lam (fun x => -f x) := by
  refine ⟨?_, fun t => by simpa [corr] using h.flat t⟩
  intro x
  rcases h.ternary x with hx | hx | hx <;> simp [hx]

theorem IsSDS.translate {k lam : ℤ} {f : G → ℤ} (h : IsSDS k lam f) (a : G) :
    IsSDS k lam (fun x => f (x+a)) := by
  refine ⟨fun x => h.ternary _, ?_⟩
  intro t
  rw [← h.flat t]
  simpa only [corr, add_right_comm _ a t] using
    sum_translate (fun x => f x * f (x+t)) a

theorem negative_count {k lam : ℤ} {f : G → ℤ} (h : IsSDS k lam f) :
    2 * ((univ.filter (fun x => f x = -1)).card : ℤ) = k - ∑ x : G, f x := by
  rw [← sum_boole, Finset.mul_sum, ← show corr f 0 = k by simpa using h.flat 0]
  simp only [corr, add_zero]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro x _
  rcases h.ternary x with hx | hx | hx <;> norm_num [hx]

theorem pullback {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {k lam : ℤ} {f : G → ℤ} (h : IsSDS k lam f) (e : H ≃+ G) :
    IsSDS k lam (fun x => f (e x)) := by
  refine ⟨fun x => h.ternary _, ?_⟩
  intro t
  have he : corr (fun x => f (e x)) t = corr f (e t) := by
    unfold corr
    apply Fintype.sum_equiv e.toEquiv
    intro x
    simp
  simpa [he] using h.flat (e t)

end Signed39
