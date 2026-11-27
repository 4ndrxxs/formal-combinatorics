import SignedCrossRows

/-! Mixed-row residue bounds obtained by summing a correlation variance over all partner rows. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {p : ℕ} [Fact p.Prime]

omit [DecidableEq H] in
theorem cross_mass (a b : H → ℤ) : mass (cross a b)=mass a*mass b := by
  unfold mass cross
  rw [sum_comm]
  simp only [← mul_sum]
  have h (x : H) : (∑ t : H, b (x+t))=∑ t, b t :=
    Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
  simp only [h,← sum_mul]

theorem mixed_total_energy {k l : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f) (a : H → ℤ) :
    (∑ j : ZMod p, energy (cross a (row f j)))=(k-l)*energy a+l*(mass a)^2 := by
  have inner (j : ZMod p) (x y : H) :
      (∑ t : H, row f j (x+t)*row f j (y+t))=corr (row f j) (y-x) := by
    apply Fintype.sum_equiv (Equiv.addLeft x)
    intro t
    change row f j (x+t)*row f j (y+t)=row f j (x+t)*row f j ((x+t)+(y-x))
    rw [show (x+t)+(y-x)=y+t by abel]
  have allcorr (t : H) : (∑ j : ZMod p, corr (row f j) t)=(if t=0 then k-l else 0)+l := by
    have h : (∑ j : ZMod p, corr (row f j) t)=corr f (0,t) := by simp [corr,row,Fintype.sum_prod_type]
    rw [h,hf.flat]
    by_cases ht : t=0 <;> simp [ht,Prod.ext_iff]
  have each (j : ZMod p) : energy (cross a (row f j))=∑ x : H, ∑ y : H, a x*a y*corr (row f j) (y-x) := by
    calc
      _=∑ t : H, ∑ x : H, ∑ y : H, a x*a y*(row f j (x+t)*row f j (y+t)) := by
        simp only [energy,cross,pow_two,sum_mul,mul_sum]
        apply sum_congr rfl; intro t _
        apply sum_congr rfl; intro x _
        apply sum_congr rfl; intros; ring
      _=∑ x : H, ∑ y : H, ∑ t : H, a x*a y*(row f j (x+t)*row f j (y+t)) := by
        rw [sum_comm]; apply sum_congr rfl; intro x _; rw [sum_comm]
      _=_ := by simp only [← mul_sum,inner]
  calc
    _=∑ x : H, ∑ y : H, ∑ j : ZMod p, a x*a y*corr (row f j) (y-x) := by
      simp only [each]; rw [sum_comm]; apply sum_congr rfl; intro x _; rw [sum_comm]
    _=∑ x : H, ∑ y : H, ((if y=x then (k-l)*(a x)^2 else 0)+l*(a x*a y)) := by
      simp only [← mul_sum,allcorr]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro y _
      by_cases h : y=x <;> simp [h,sub_eq_zero] <;> ring
    _=_ := by simp [sum_add_distrib,← mul_sum,← sum_mul,energy,mass,pow_two]

theorem mixed_total_variance {k l : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f) (a : H → ℤ) :
    (∑ j : ZMod p, variance (cross a (row f j)))=(k-l)*variance a := by
  have ss : (∑ j : ZMod p, (mass (row f j))^2)=k-l+(Fintype.card H:ℤ)*l := by
    change energy (rowMass f)=_
    simpa [energy_zero] using rowmass_corr hf 0
  simp only [variance,sum_sub_distrib,← mul_sum,cross_mass,mul_pow,ss,mixed_total_energy hf]
  ring

omit [AddCommGroup H] [DecidableEq H] in
theorem variance_affine (a : H → ℤ) (h t : ℤ) :
    variance (fun x => h+t*a x)=t^2*variance a := by
  have he (x y : H) : ((h+t*a x)-(h+t*a y))^2=t^2*(a x-a y)^2 := by ring
  have eq := pairwise_variance (fun x => h+t*a x)
  simp only [he,← mul_sum,pairwise_variance] at eq
  linarith

def residueCost (inv m a b : ℤ) : ℤ :=
  let r := (inv*a*b)%m
  r*(m-r)

theorem mixed_pair_lower {k l s inv w : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (hn : k-l=(p:ℤ)*s) (hs : ¬ (p:ℤ)∣s) (hc : p.Coprime (Fintype.card H))
    (hu : (p:ℤ)*inv=1+(Fintype.card H:ℤ)*w) (i j : ZMod p) :
    (p:ℤ)^2*residueCost inv (Fintype.card H) (rowMass f i) (rowMass f j)
      ≤variance (cross (row f i) (row f j)) := by
  let h := cross (row f i) (row f j)
  let c := h 0
  let m : ℤ := Fintype.card H
  have dvd (t : H) : (p:ℤ)∣h t-c := by
    have d := dvd_sub (row_cross_dvd hf hn hc i j t) (row_cross_dvd hf hn hc i j 0)
    have e : (p:ℤ)∣s*(h t-c) := by convert d using 1; dsimp [c,h]; ring
    exact ((Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_or_dvd e).resolve_left hs
  choose z hz using dvd
  have eq : h=fun t => c+(p:ℤ)*z t := funext (fun t => by have e:=hz t; omega)
  have he : mass h=m*c+(p:ℤ)*mass z := calc
    _=mass (fun t => c+(p:ℤ)*z t) := congrArg mass eq
    _=_ := by simp [mass,sum_add_distrib,← mul_sum,m]
  have hm : mass h=rowMass f i*rowMass f j := cross_mass _ _
  have modEq : mass z ≡ inv*(rowMass f i)*(rowMass f j) [ZMOD m] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨inv*c+w*mass z,?_⟩
    change (p:ℤ)*inv=1+m*w at hu
    linear_combination -inv*hm+inv*he+(mass z)*hu
  have lb := residue_variance z
  change (mass z%m)*(m-mass z%m)≤variance z at lb
  rw [show mass z%m=inv*(rowMass f i)*(rowMass f j)%m from modEq] at lb
  calc
    _≤(p:ℤ)^2*variance z := mul_le_mul_of_nonneg_left lb (sq_nonneg _)
    _=variance (fun t => c+(p:ℤ)*z t) := (variance_affine z c p).symm
    _=_ := congrArg variance eq.symm

/-- The variance of one row bounds the total residue cost of all row-mass products with that row. -/
theorem mixed_anchor_bound {k l s inv w : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (hn : k-l=(p:ℤ)*s) (hs : ¬ (p:ℤ)∣s) (hc : p.Coprime (Fintype.card H))
    (hu : (p:ℤ)*inv=1+(Fintype.card H:ℤ)*w) (i : ZMod p) :
    (p:ℤ)*(∑ j : ZMod p, residueCost inv (Fintype.card H) (rowMass f i) (rowMass f j))
      ≤ s*variance (row f i) := by
  have h := sum_le_sum (s:=univ) (fun j _ => mixed_pair_lower hf hn hs hc hu i j)
  rw [← mul_sum,mixed_total_variance hf,hn] at h
  have positive : 0 < (p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  apply (mul_le_mul_iff_right₀ positive).mp
  linear_combination h

/-- The sum over all ordered pairs of rows is bounded solely by s and |H|. -/
theorem mixed_global_bound {k l s inv w : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (hn : k-l=(p:ℤ)*s) (hs : ¬ (p:ℤ)∣s) (hc : p.Coprime (Fintype.card H))
    (hu : (p:ℤ)*inv=1+(Fintype.card H:ℤ)*w) :
    (∑ i : ZMod p, ∑ j : ZMod p, residueCost inv (Fintype.card H) (rowMass f i) (rowMass f j))
      ≤ s^2*((Fintype.card H:ℤ)-1) := by
  have h := sum_le_sum (s:=univ) (fun i _ => mixed_anchor_bound hf hn hs hc hu i)
  simp only [← mul_sum,total_row_variance hf,hn] at h
  have positive : 0 < (p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  apply (mul_le_mul_iff_right₀ positive).mp
  linear_combination h

#print axioms mixed_anchor_bound
#print axioms mixed_global_bound

end Signed39.Contraction
