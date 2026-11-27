import SignedPrimeNorm

/-! Necessary conditions on the mass and the support size of each row. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {p : ℕ} [Fact p.Prime]

omit [AddCommGroup H] [DecidableEq H] in
theorem residue_variance (b : H → ℤ) :
    let m : ℤ := Fintype.card H
    let r := mass b % m
    r*(m-r) ≤ variance b := by
  dsimp only
  let m : ℤ := Fintype.card H
  let q := mass b / m
  let r := mass b % m
  have decomp : mass b = r+m*q := (Int.emod_add_mul_ediv _ _).symm
  have lower (x : H) : b x-q ≤ (b x-q)^2 := by
    rcases le_total (b x-q) 0 with h|h
    · nlinarith [sq_nonneg (b x-q)]
    · by_cases h1 : b x-q = 0
      · simp [h1]
      · have hp : 0 ≤ b x-q-1 := by omega
        nlinarith [mul_nonneg h hp]
  have he : (∑ x : H, (b x-q)^2) = energy b - 2*q*mass b + m*q^2 := by
    calc
      _ = ∑ x : H, ((b x)^2-2*q*b x+q^2) := by apply sum_congr rfl; intro x _; ring
      _ = _ := by simp [sum_add_distrib,sum_sub_distrib,← mul_sum,energy,mass,m]
  have h := sum_le_sum (s := univ) (fun x _ => lower x)
  rw [he,sum_sub_distrib] at h
  change mass b - (∑ _ : H, q) ≤ _ at h
  simp only [sum_const,card_univ,nsmul_eq_mul] at h
  change mass b-m*q ≤ energy b-2*q*mass b+m*q^2 at h
  rw [decomp] at h
  change r*(m-r) ≤ m*energy b-(mass b)^2
  rw [decomp]
  have hm' : (0:ℤ) ≤ m := Nat.cast_nonneg _
  nlinarith [mul_nonneg hm' (sub_nonneg.mpr h)]

omit [AddCommGroup H] [DecidableEq H] in
theorem energy_scale (a : H → ℤ) (q : ℤ) : energy (fun x => q*a x) = q^2*energy a := by
  simp only [energy,mul_pow, ← mul_sum]

omit [AddCommGroup H] [DecidableEq H] in
theorem mass_fiber (f : ZMod p × H → ℤ) : mass (fiber f) = mass f := by
  simp only [mass,fiber,Fintype.sum_prod_type]
  rw [sum_comm]

def admissibleRow (p m s lam c a b : ℤ) : Prop :=
  -b ≤ a ∧ a ≤ b ∧ 0 ≤ b ∧ b ≤ m ∧ 2 ∣ b-a ∧ p ∣ s*b+lam*a^2 ∧
  p*(c*a % m)*(m-(c*a % m)) ≤ s*(m*b-a^2)

instance (p m s lam c a b : ℤ) : Decidable (admissibleRow p m s lam c a b) := by
  unfold admissibleRow
  infer_instance

theorem row_admissible {k lam s c : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*s) (hmass : mass f=(p:ℤ)*c) (hc : p.Coprime (Fintype.card H)) (i : ZMod p) :
    admissibleRow p (Fintype.card H) s lam c (mass (row f i)) (energy (row f i)) := by
  let u := row f i
  let a := mass u
  let b := energy u
  let m : ℤ := Fintype.card H
  have ht (x : H) : u x= -1 ∨ u x=0 ∨ u x=1 := hf.ternary (i,x)
  have ha : -b ≤ a := by
    change -(∑ x, u x ^ 2) ≤ ∑ x, u x
    rw [← sum_neg_distrib]
    exact sum_le_sum (fun x _ => by rcases ht x with e|e|e <;> norm_num [e])
  have ha' : a ≤ b := sum_le_sum (fun x _ => by rcases ht x with e|e|e <;> norm_num [e])
  have hb : 0 ≤ b := sum_nonneg (fun x _ => sq_nonneg _)
  have hb' : b ≤ m := calc
    _ ≤ ∑ _ : H, (1:ℤ) := sum_le_sum (fun x _ => by rcases ht x with e|e|e <;> norm_num [e])
    _ = _ := by simp [m]
  have hpar : 2 ∣ b-a := by
    change 2 ∣ (∑ x, u x ^ 2) - ∑ x, u x
    rw [← sum_sub_distrib]
    exact dvd_sum (fun x _ => by rcases ht x with e|e|e <;> norm_num [e])
  choose w hw using (matched_dvd hf ⟨s,hn⟩ hc i)
  have hid : matched u (fiber f) = fun z => (p:ℤ)*w z := funext hw
  have h1 := matched_energy u (fiber f) (k-lam) ((Fintype.card (ZMod p):ℤ)*lam) (fiber_flat hf)
  rw [hid,energy_scale,ZMod.card,hn] at h1
  have hp : 0 < (p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have he : (p:ℤ)*energy w = s*b+lam*a^2 := by
    apply mul_left_cancel₀ hp.ne'
    linear_combination h1
  have h2 := matched_mass u (fiber f)
  rw [hid,mass_fiber,hmass] at h2
  have hlast : mass w=c*a := by
    apply mul_left_cancel₀ hp.ne'
    change (∑ z, (p:ℤ)*w z) = a*((p:ℤ)*c) at h2
    rw [← mul_sum] at h2
    change (p:ℤ)*(∑ z, w z) = (p:ℤ)*(c*a)
    linear_combination h2
  have min := residue_variance w
  change (mass w%m)*(m-mass w%m) ≤ m*energy w-(mass w)^2 at min
  rw [hlast] at min
  have full := sds_mass hf
  rw [hn,hmass,Fintype.card_prod,ZMod.card,Nat.cast_mul] at full
  change ((p:ℤ)*c)^2 = p*s + ((p:ℤ)*m)*lam at full
  have hmass2 : (p:ℤ)*c^2 = s+m*lam := by
    apply mul_left_cancel₀ hp.ne'
    linear_combination full
  refine ⟨ha,ha',hb,hb',hpar,⟨energy w,he.symm⟩,?_⟩
  change (p:ℤ)*(c*a%m)*(m-c*a%m) ≤ s*(m*b-a^2)
  calc
    _ ≤ (p:ℤ)*(m*energy w-(c*a)^2) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left min hp.le
    _ = _ := by linear_combination m*he - a^2*hmass2

end Signed39.Contraction
