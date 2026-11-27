import SignedSevenCases
import SignedMultiplierOrbits

namespace Signed39.Profiles

open Finset Contraction

local instance : Fact (Nat.Prime 7):=⟨by decide⟩
local instance : Fact (Nat.Prime 31):=⟨by decide⟩

private def scalarSeven : ZMod 31 ≃+ ZMod 31 where
  toFun x:=7*x
  invFun x:=7⁻¹*x
  left_inv x:=by simp only [←mul_assoc,inv_mul_cancel₀ (by decide : (7:ZMod 31)≠0),one_mul]
  right_inv x:=by simp only [←mul_assoc,mul_inv_cancel₀ (by decide : (7:ZMod 31)≠0),one_mul]
  map_add' x y:=by ring

private def ranks : List ℤ := [0,0,12,0,9,10,12,14,6,1,7,11,9,5,11,10,3,3,13,2,4,14,8,13,6,5,2,1,8,4,7]

theorem no_unsigned_31 (u : ZMod 31 → ℤ) (range : ∀x, u x=0∨u x=1) (mu : mass u=21)
    (flat : ∀t,corr u t=(if t=0 then 7 else 0)+14) : False := by
  let E:=scalarSeven
  have div (t:ZMod 31) : (7:ℤ)∣matched (fun x=>u (E.symm x)) u t-14 :=
    prime_multiplier_dvd (q:=7) u 7 14 flat (by decide) (by rw [ZMod.card]; decide) E 1
      (fun x=>by simp [E,scalarSeven,nsmul_eq_mul]) t
  obtain ⟨t,matchEq⟩:=integral_match_translation u 7 14 (by decide) flat E div
  let base : ZMod 31:=26*t
  let g (x : ZMod 31):=u (x+base)
  have six : 6*base=t := by dsimp [base]; rw [←mul_assoc,show (6:ZMod 31)*26=1 by decide,one_mul]
  have fix (x:ZMod 31) : g (E x)=g x := by
    have h:=matchEq (E (x+base))
    rw [E.symm_apply_apply] at h
    change u (x+base)=u (7*(x+base)-t) at h
    change u (7*x+base)=u (x+base)
    rw [show 7*(x+base)-t=7*x+base by linear_combination six] at h
    exact h.symm
  have checks : ∀x : ZMod 31, (15:ℤ)∣(if x=0 then (0:ℤ) else 1)+ranks.getD (7*x:ZMod 31).val 0-ranks.getD x.val 0 := by decide +kernel
  have dv:=orbit_mass_dvd E.toEquiv g (fun x=>ranks.getD x.val 0) 15 0 fix checks
  have mg : mass g=21 := (sum_translate u base).trans mu
  change (15:ℤ)∣mass g-u (0+base) at dv
  rw [mg,zero_add] at dv
  rcases range base with z|o
  · rw [z] at dv; norm_num at dv
  · rw [o] at dv; norm_num at dv

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem unsigned_row_false {f : ZMod 7 × H → ℤ} (hf : IsSDS 144 32 f) (hm : Fintype.card H=31) (i : ZMod 7)
    (mass21 : rowMass f i=21) (weight21 : energy (row f i)=21) : False := by
  let u:=row f i
  have mu : mass u=21 := mass21
  have eu : energy u=21 := weight21
  have pos (x:H) : 0≤(u x)^2-u x := by rcases hf.ternary (i,x) with h|h|h <;> change u x=_ at h <;> norm_num [h]
  have noNeg : (∑x:H,((u x)^2-u x))=0 := by rw [sum_sub_distrib]; change energy u-mass u=0; omega
  have range (x:H) : u x=0 ∨ u x=1 := by
    have h:=(sum_eq_zero_iff_of_nonneg (fun z _=>pos z)).mp noNeg x (mem_univ x)
    rcases hf.ternary (i,x) with neg|z|o
    · change u x= -1 at neg; norm_num [neg] at h
    · exact Or.inl z
    · exact Or.inr o
  have lower (t:H) : 14≤corr u t := by
    have non : 0≤∑x:H,(1-u x)*(1-u (x+t)) := sum_nonneg (fun x _=>mul_nonneg (by rcases range x with h|h <;> omega) (by rcases range (x+t) with h|h <;> omega))
    have sumShift : (∑x:H,u (x+t))=21 := (sum_translate u t).trans mu
    have expand : (∑x:H,(1-u x)*(1-u (x+t)))=(Fintype.card H:ℤ)-mass u-(∑x:H,u (x+t))+corr u t := by
      calc
        _=∑x:H,((1:ℤ)-u x-u (x+t)+u x*u (x+t)) := by apply sum_congr rfl; intros; ring
        _=_ := by simp only [sum_add_distrib,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one,corr,mass]
    rw [expand,hm,mu,sumShift] at non
    have dv:=row_displacement_dvd (s:=16) hf (by decide) (by decide) (hm ▸ (by decide : Nat.Coprime 7 31)) i t
    change (7:ℤ)∣energy u-corr u t at dv
    rw [eu] at dv
    omega
  let goal (t:H):= (if t=0 then (7:ℤ) else 0)+14
  have bound (t:H) : 0≤corr u t-goal t := by
    by_cases z:t=0
    · simp [z,goal,←energy_zero,eu]
    · simpa [goal,z] using sub_nonneg.mpr (lower t)
  have full : (∑t:H, (corr u t-goal t))=0 := by
    have smc : (∑t:H,corr u t)=441 := by change mass (cross u u)=441; rw [cross_mass,mu]; decide
    rw [sum_sub_distrib,smc]
    simp [goal,sum_add_distrib,hm]
  have flat (t:H) : corr u t=(if t=0 then 7 else 0)+14 :=
    sub_eq_zero.mp ((sum_eq_zero_iff_of_nonneg (fun z _=>bound z)).mp full t (mem_univ t))
  have order : Nat.card H=31 := Nat.card_eq_fintype_card.trans hm
  let e : ZMod 31 ≃+ H := (ZMod.ringEquivCongr order.symm).toAddEquiv.trans (zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card order))
  let v (x:ZMod 31):=u (e x)
  apply no_unsigned_31 v (fun x=>range (e x)) ((Fintype.sum_equiv e.toEquiv _ _ (fun _=>rfl)).trans mu)
  intro t
  have eq : corr v t=corr u (e t) := Fintype.sum_equiv e.toEquiv _ _ (fun x=>by dsimp [v]; rw [map_add])
  rw [eq,flat]
  simp

theorem no_217_144_32 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hg : Fintype.card G=217) : ¬∃f : G → ℤ, IsSDS 144 32 f := by
  apply seven_reduction G (m:=31) (c:=12) hg (by decide) (by decide)
  intro H _ _ _ hm f hf hs
  obtain ⟨L,mem,actual,loc,low⟩:=seven_rows (inv:=9) (w:=2) hf hm (by decide) (by decide) (by decide) hs (by decide)
  have rule : ∀L∈sevenPatterns,lowTotal 31 144 32 12 9 (shifted 12 L)≤144 → shifted 12 L=[10,10,10,11,11,11,21] := by decide +kernel
  have eq:=rule L mem low
  rw [eq] at actual loc
  obtain ⟨i,hi⟩:∃i,rowMass f i=21 := (seven_mem _ _).mp (actual.mem_iff.mpr (by decide))
  have b:=loc i
  rw [hi] at b
  have single : weights 31 144 32 12 9 [10,10,10,11,11,11,21] 21=[21] := by decide +kernel
  rw [single,List.mem_singleton] at b
  exact unsigned_row_false hf hm i hi b

#print axioms no_217_144_32

end Signed39.Profiles
