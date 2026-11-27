import SignedPrimeNorm

/-! Projection of an integral word to an arbitrary additive quotient. -/

namespace Signed39.Contraction

open Finset

variable {G K : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup K] [Fintype K] [DecidableEq K]

def projected (φ : G →+ K) (f : G → ℤ) (t : K) : ℤ :=
  ∑ x, if φ x=t then f x else 0

omit [DecidableEq G] in
theorem projected_corr (φ : G →+ K) (f : G → ℤ) (t : K) :
    corr (projected φ f) t = projected φ (corr f) t := by
  classical
  have shift (x : G) : projected φ f (φ x+t) = ∑ z : G, if φ z=t then f (x+z) else 0 := by
    apply Fintype.sum_equiv (Equiv.addLeft x).symm
    intro z
    change (if φ z=φ x+t then f z else 0) = if φ (-x+z)=t then f (x+(-x+z)) else 0
    simp [neg_add_eq_iff_eq_add]
  calc
    _ = ∑ x : G, f x*projected φ f (φ x+t) := by
      unfold corr
      conv_lhs => arg 2; intro y; lhs; unfold projected
      simp only [sum_mul,ite_mul,zero_mul]
      rw [sum_comm]
      simp
    _ = ∑ z : G, if φ z=t then corr f z else 0 := by
      simp only [shift,mul_sum,mul_ite,mul_zero]
      rw [sum_comm]
      apply sum_congr rfl
      intro z _
      by_cases h : φ z=t <;> simp [h,corr]
    _ = _ := rfl

theorem projected_flat (φ : G →+ K) (hφ : Function.Surjective φ) {k lam : ℤ} {f : G → ℤ}
    (hf : IsSDS k lam f) (t : K) :
    corr (projected φ f) t = (if t=0 then k-lam else 0)+(Nat.card φ.ker:ℤ)*lam := by
  classical
  rw [projected_corr,projected]
  have separate (x : G) : (if φ x = t then corr f x else 0) =
      (if x=0 then (if t=0 then k-lam else 0) else 0)+(if φ x=t then lam else 0) := by
    rw [hf.flat]
    by_cases h : x=0
    · subst x; by_cases ht : t=0 <;> simp [ht,eq_comm]
    · by_cases ht : φ x=t <;> simp [h,ht]
  simp only [separate,sum_add_distrib,sum_ite_eq',mem_univ,ite_true]
  congr 1
  have card : Nat.card {x // φ x = t} = Nat.card φ.ker :=
    Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hφ t)
  rw [sum_ite]
  simpa [← Fintype.card_subtype,← Nat.card_eq_fintype_card] using congrArg (fun a : ℕ => (a:ℤ)*lam) card

omit [DecidableEq G] in
theorem exists_prime_quotient (q : ℕ) (hq : q.Prime) (h : q ∣ Fintype.card G) :
    ∃ φ : G →+ ZMod q, Function.Surjective φ := by
  classical
  obtain ⟨ι,_,n,hn,⟨e₀⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  have (i : ι) : NeZero (n i) := NeZero.of_gt (hn i)
  let e := e₀.trans (DirectSum.addEquivProd _)
  have hc : Fintype.card G = ∏ i, n i := by simpa [Fintype.card_pi,ZMod.card] using Fintype.card_congr e.toEquiv
  obtain ⟨i,_,hi⟩ := (hq.prime.dvd_finsetProd_iff n).mp (hc ▸ h)
  let φ := (ZMod.castHom hi (ZMod q)).toAddMonoidHom.comp
            ((Pi.evalAddMonoidHom (fun j => ZMod (n j)) i).comp e.toAddMonoidHom)
  refine ⟨φ,?_⟩
  intro y
  obtain ⟨x,hx⟩ := ZMod.castHom_surjective hi y
  exact ⟨e.symm (Pi.single i x),by simpa [φ] using hx⟩

theorem even_norm_square {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (heven : 2 ∣ Fintype.card G) : IsSquare (k-lam) := by
  obtain ⟨φ,hφ⟩ := exists_prime_quotient 2 (by decide) heven
  exact two_flat_square (projected φ f) (ZMod.card 2) (projected_flat φ hφ hf)

theorem nonsquare_of_valuation_one {p : ℕ} (hp : p.Prime) {s : ℤ} (hs : ¬ (p:ℤ) ∣ s) :
    ¬ IsSquare ((p:ℤ)*s) := by
  rintro ⟨t,ht⟩
  have hpr := Nat.prime_iff_prime_int.mp hp
  have d : (p:ℤ) ∣ t^2 := ⟨s,by simpa [pow_two] using ht.symm⟩
  obtain ⟨z,hz⟩ := hpr.dvd_of_dvd_pow d
  apply hs
  refine ⟨z^2,?_⟩
  apply mul_left_cancel₀ hpr.ne_zero
  rw [hz] at ht
  linear_combination ht

#print axioms even_norm_square

end Signed39.Contraction
