import SignedClassicalMultiplier

namespace Signed39.Template

open Finset Contraction

variable {p : ℕ} [Fact p.Prime]

theorem signed_match_pointwise {H:Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (u w:H→ℤ) {E:ℤ} (eu:energy u=E) (ew:energy w=E) (t:H) (sg:ℤ) (sg2:sg^2=1)
    (h : matched u w t=sg*E) : ∀x,u x=sg*w (x-t) := by
  have es : (∑x,(w (x-t))^2)=E := by simpa [sub_eq_add_neg,energy] using (sum_translate (fun x=>(w x)^2) (-t)).trans ew
  have total : (∑x,(u x-sg*w (x-t))^2)=0 := calc
    _=∑x,((u x)^2+sg^2*(w (x-t))^2-2*sg*(u x*w (x-t))) := by apply sum_congr rfl; intros; ring
    _=_ := by
      simp only [sum_sub_distrib,sum_add_distrib,←mul_sum,es]
      change energy u+sg^2*E-2*sg*matched u w t=0
      rw [eu,h,sg2]
      linear_combination -2*E*sg2
  intro x
  have a:=(sum_eq_zero_iff_of_nonneg (fun x _=>sq_nonneg (u x-sg*w (x-t)))).mp total x (mem_univ x)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp a)

theorem template_match_11 (u w:ZMod 11→ℤ) (mu:mass u=0) (eu:energy u=230)
    (ew:energy w=230) (flat:∀t,corr w t=(if t=0 then 253 else 0)-23)
    (modulus:∀t,(253:ℤ)∣matched u w t-matched u w 0) :
    ∃(t:ZMod 11)(sg:ℤ),(sg=1∨sg= -1) ∧ ∀x,u x=sg*w (x-t) := by
  let h:=matched u w
  have mh : mass h=0 := by rw [show mass h=mass u*mass w from matched_mass _ _,mu,zero_mul]
  have ve:=matched_variance u w 253 (-23) flat
  change variance h=253*variance u at ve
  rw [variance,variance,ZMod.card,mu,mh,eu] at ve
  have eh : energy h=58190 := by omega
  have shift (t:ZMod 11) : (∑x,(w (x-t))^2)=230 := by
    simpa [energy,sub_eq_add_neg] using (sum_translate (fun x=>(w x)^2) (-t)).trans ew
  have bound (t:ZMod 11) (sg:ℤ) (s2:sg^2=1) : 0≤460-2*sg*h t := by
    have z : 0≤∑x,(u x-sg*w (x-t))^2 := sum_nonneg (fun _ _=>sq_nonneg _)
    have e (x:ZMod 11) : (u x-sg*w (x-t))^2=(u x)^2+sg^2*(w (x-t))^2-2*sg*(u x*w (x-t)) := by ring
    simp only [e,sum_sub_distrib,sum_add_distrib,←mul_sum,shift,s2,one_mul] at z
    change 0≤energy u+230-2*sg*h t at z
    rwa [eu] at z
  let r:=h 0%253
  have r0 : 0≤r := Int.emod_nonneg _ (by decide)
  have r1 : r<253 := Int.emod_lt_of_pos _ (by decide)
  have pair (t:ZMod 11) : h t=r ∨ h t=r-253 := by
    obtain ⟨j,hj⟩:=modulus t
    change h t-h 0=253*j at hj
    have w:=Int.emod_add_mul_ediv (h 0) 253
    change r+253*(h 0/253)=h 0 at w
    have hi:=bound t 1 (by decide)
    have lo:=bound t (-1) (by decide)
    omega
  have pt (t:ZMod 11) : (h t)^2-(2*r-253)*h t+r*(r-253)=0 := by rcases pair t with a|a <;> rw [a] <;> ring
  have total := sum_congr (s₁:=univ) rfl (fun t _=>pt t)
  simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_zero] at total
  change energy h-(2*r-253)*mass h+r*(11*r-11*253)=0 at total
  rw [eh,mh,mul_zero,sub_zero] at total
  have roots : (r-23)*(r-230)=0 := by
    have key : 11*((r-23)*(r-230))=0 := by linear_combination total
    omega
  have witness : ∃t:ZMod 11,h t=230∨h t= -230 := by
    by_contra! wrong
    rcases mul_eq_zero.mp roots with r23|r230
    · have c (t:ZMod 11) : h t=23 := by have a:=pair t; have b:=wrong t; omega
      have bad : mass h=253 := by simp [mass,c,ZMod.card]
      omega
    · have c (t:ZMod 11) : h t= -23 := by have a:=pair t; have b:=wrong t; omega
      have bad : mass h= -253 := by simp [mass,c,ZMod.card]
      omega
  obtain ⟨t,pos|neg⟩:=witness
  · exact ⟨t,1,Or.inl rfl,signed_match_pointwise u w eu ew t 1 (by decide) (by simpa [h] using pos)⟩
  · exact ⟨t,-1,Or.inr rfl,signed_match_pointwise u w eu ew t (-1) (by decide) (by simpa [h] using neg)⟩

#print axioms template_match_11

end Signed39.Template
