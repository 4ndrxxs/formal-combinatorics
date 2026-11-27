import SignedClassicalMultiplier

/-! The classical self-conjugacy obstruction on the whole group, used for a published case. -/

namespace Signed39.Contraction

open Finset

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {q : ℕ} [Fact q.Prime]

theorem self_conjugate_differences {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f)
    (nq : (q:ℤ)∣k-l) (qm : ¬(q:ℤ)∣(Fintype.card G:ℤ)) {e : ℕ} (positive : 0<e)
    (inverse : ∀x:G,q^e • x= -x) (x y : G) : (q:ℤ)∣f x-f y := by
  let m : ℤ := Fintype.card G
  let u := fun x =>m*f x-mass f
  have total := sds_mass hf
  change (mass f)^2=k-l+m*l at total
  have ca (v : G → ℤ) (t : G) : corr v t=matched v v (-t) := by simp [corr,matched]
  have all (t : G) : (q:ℤ)∣corr u t := by
    rw [ca]; dsimp only [u,m]; rw [centered_match,←ca,hf.flat]
    obtain ⟨b,eq⟩ := nq
    by_cases t0:t=0
    · simp only [t0,ite_true]
      refine ⟨(m^2-m)*b,?_⟩
      change m^2*k-m*mass f*mass f=_
      linear_combination -m*total+(m^2-m)*eq
    · simp only [ite_eq_right t0]
      refine ⟨-m*b,?_⟩
      change m^2*l-m*mass f*mass f=_
      linear_combination -m*total-m*eq
  have coeff:=self_conjugate_coefficients u e positive inverse all
  have dw := dvd_sub (coeff x) (coeff y)
  have whole : (q:ℤ)∣m*(f x-f y) := by convert dw using 1; dsimp only [u]; ring
  exact ((Nat.prime_iff_prime_int.mp (Fact.out:q.Prime)).dvd_or_dvd whole).resolve_left qm

theorem full_conjugate_exclusion {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (nq : (q:ℤ)∣k-l)
    (neq : k≠l) (q3 : 3≤q) (qm : ¬(q:ℤ)∣(Fintype.card G:ℤ)) (long : 1<Fintype.card G)
    {e : ℕ} (positive : 0<e) (inverse : Fintype.card G∣q^e+1) : False := by
  have acts (x:G) : q^e • x= -x := by
    have dv : addOrderOf x∣q^e+1 := (addOrderOf_dvd_card (x:=x)).trans inverse
    have nil : (q^e+1) • x=0 := (addOrderOf_dvd_iff_nsmul_eq_zero).mp dv
    rw [add_smul,one_smul] at nil
    exact eq_neg_of_add_eq_zero_left nil
  have fixed (x:G) : f x=f 0 := by
    obtain ⟨w,hw⟩ := self_conjugate_differences hf nq qm positive acts x 0
    have hx := hf.ternary x
    have hz := hf.ternary 0
    have low : -2≤f x-f 0 := by omega
    have high : f x-f 0≤2 := by omega
    by_cases z : w=0
    · rw [z,mul_zero] at hw; omega
    have q0 : 0≤(q:ℤ) := Nat.cast_nonneg _
    rcases lt_or_gt_of_ne z with neg|pos
    · have prod := mul_le_mul_of_nonneg_left (show w≤ -1 by omega) q0
      simp only [mul_neg,mul_one] at prod
      omega
    · have prod := mul_le_mul_of_nonneg_left (show 1≤w by omega) q0
      simp only [mul_one] at prod
      omega
  obtain ⟨x,y,diff⟩ := Fintype.one_lt_card_iff.mp long
  let z := x-y
  have nz : z≠0 := sub_ne_zero.mpr diff
  have same : corr f z=corr f 0 := by unfold corr; apply sum_congr rfl; intros; rw [fixed (_+z),fixed (_+0)]
  rw [hf.flat,hf.flat] at same
  simp only [ite_eq_right nz,ite_true] at same
  exact neq same.symm

theorem full_217_148_22 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hg : Fintype.card G=217) : ¬∃f : G → ℤ, IsSDS 148 22 f := by
  rintro ⟨f,hf⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact full_conjugate_exclusion (q:=3) hf (by decide) (by decide) (by decide) (by rw [hg]; decide)
    (by rw [hg]; decide) (e:=15) (by decide) (by rw [hg]; decide)

#print axioms full_217_148_22

end Signed39.Contraction
