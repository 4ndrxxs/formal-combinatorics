import SignedMoments

/-! The order of any signed difference set of nonsquare norm n is at most n²+n+1. -/

namespace Signed39.Contraction

open Finset

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem absolute_order_bound {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hn : 0 < k-lam) (hnonsquare : ¬ IsSquare (k-lam)) :
    (Fintype.card G:ℤ) ≤ (k-lam)^2+(k-lam)+1 := by
  let n := k-lam
  let v : ℤ := Fintype.card G
  have vpos : 0 < v := by dsimp [v]; exact_mod_cast Fintype.card_pos
  have npos : 0 < n := hn
  have he : energy f=k := by rw [energy_zero,hf.flat]; simp
  have hmass : (mass f)^2 = n+v*lam := sds_mass hf
  have vsteps : variance f = (v-1)*n := by
    change v*energy f-(mass f)^2 = _
    rw [he,hmass]; dsimp [n]; ring
  let r := mass f % v
  let t := min r (v-r)
  have r0 : 0 ≤ r := Int.emod_nonneg _ vpos.ne'
  have rv : r < v := Int.emod_lt_of_pos _ vpos
  have t0 : 0 ≤ t := le_min r0 (by omega)
  have tsmall : 2*t ≤ v := by dsimp [t]; omega
  have tcase : t=r ∨ t=v-r := min_choice _ _
  have lower := residue_variance f
  change r*(v-r) ≤ variance f at lower
  rw [vsteps] at lower
  have hprod : t*(v-t) ≤ (v-1)*n := by rcases tcase with h|h <;> rw [h] <;> nlinarith
  have congr_r : (r^2) % v = n % v := by
    subst r
    have e : ((mass f % v)^2)%v = ((mass f)^2)%v := by simp [pow_two,Int.mul_emod]
    rw [e,hmass,Int.add_emod]
    simp
  have congr_t : (t^2) % v = n % v := by
    rcases tcase with e|e
    · simpa only [e] using congr_r
    · rw [e,show (v-r)^2 = r^2+v*(v-2*r) by ring,Int.add_emod]
      simpa using congr_r
  by_contra! large
  change n^2+n+1 < v at large
  have tn : t ≤ n := by
    by_contra! bad
    have h₁ : 0 ≤ t-(n+1) := by omega
    have h₂ : 0 ≤ v-t-(n+1) := by omega
    nlinarith [mul_nonneg h₁ h₂]
  have tsq : t^2 ≤ n^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr tn) (show 0≤n+t by omega)]
  have sq_lt : t^2 < v := by omega
  have n_lt : n < v := by nlinarith [sq_nonneg n]
  rw [Int.emod_eq_of_lt (sq_nonneg _) sq_lt,Int.emod_eq_of_lt npos.le n_lt] at congr_t
  exact hnonsquare ⟨t,by simpa [pow_two,n] using congr_t.symm⟩

#print axioms absolute_order_bound

end Signed39.Contraction
