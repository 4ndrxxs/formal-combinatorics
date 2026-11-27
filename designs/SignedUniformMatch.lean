import SignedTemplateMatch
import SignedModularSupport
import SignedPrimePowerMultiplier

namespace Signed39.Template

open Finset Contraction

variable {p : ℕ} [Fact p.Prime]

theorem uniform_signed_match (u w : ZMod p → ℤ) (s : ℤ) (positive : 0<s)
    (mu:mass u=0) (eu:energy u=(p:ℤ)*s-s) (ew:energy w=(p:ℤ)*s-s)
    (flat:∀t,corr w t=(if t=0 then (p:ℤ)*s else 0)-s)
    (modulus:∀t,(p:ℤ)*s∣matched u w t-matched u w 0) :
    ∃(t:ZMod p)(sg:ℤ),(sg=1∨sg= -1) ∧ ∀x,u x=sg*w (x-t) := by
  let n:ℤ:=(p:ℤ)*s
  let E:=n-s
  let h:=matched u w
  have pp : (0:ℤ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have nn : 0<n := mul_pos pp positive
  have eu' : energy u=E := eu
  have ew' : energy w=E := ew
  have mh : mass h=0 := by rw [show mass h=mass u*mass w from matched_mass _ _,mu,zero_mul]
  have ve:=matched_variance u w n (-s) flat
  change variance h=n*variance u at ve
  rw [variance,variance,ZMod.card,mu,mh,eu'] at ve
  have eh : energy h=n*E := by
    apply mul_left_cancel₀ pp.ne'
    linear_combination ve
  have shift (t:ZMod p) : (∑x,(w (x-t))^2)=E := by
    simpa [energy,sub_eq_add_neg] using (sum_translate (fun x=>(w x)^2) (-t)).trans ew'
  have bound (t:ZMod p) (sg:ℤ) (s2:sg^2=1) : 0≤2*E-2*sg*h t := by
    have z : 0≤∑x,(u x-sg*w (x-t))^2 := sum_nonneg (fun _ _=>sq_nonneg _)
    have ex (x:ZMod p) : (u x-sg*w (x-t))^2=(u x)^2+sg^2*(w (x-t))^2-2*sg*(u x*w (x-t)) := by ring
    simp only [ex,sum_sub_distrib,sum_add_distrib,←mul_sum,shift,s2,one_mul] at z
    change 0≤energy u+E-2*sg*h t at z
    rw [eu'] at z
    linarith only [z]
  let r:=h 0%n
  have r0 : 0≤r := Int.emod_nonneg _ nn.ne'
  have r1 : r<n := Int.emod_lt_of_pos _ nn
  have pair (t:ZMod p) : h t=r ∨ h t=r-n := by
    obtain ⟨j,hj⟩:=modulus t
    change h t-h 0=n*j at hj
    have w:=Int.emod_add_mul_ediv (h 0) n
    change r+n*(h 0/n)=h 0 at w
    let z:=j+h 0/n
    have eq : h t=r+n*z := by dsimp only [z]; linear_combination hj-w
    have hi:=bound t 1 (by decide)
    have lo:=bound t (-1) (by decide)
    change 0≤2*(n-s)-2*1*h t at hi
    change 0≤2*(n-s)-2*(-1)*h t at lo
    have zlo : -1≤z := by
      by_contra! hz
      have h2:=mul_nonpos_of_nonneg_of_nonpos nn.le (show z+2≤0 by omega)
      nlinarith only [h2,eq,r1,lo,positive]
    have zhi : z≤0 := by
      by_contra! hz
      have h1:=mul_nonneg nn.le (show 0≤z-1 by omega)
      nlinarith only [h1,eq,r0,hi,positive]
    rcases (show z=0∨z= -1 by omega) with zero|neg
    · left; rwa [zero,mul_zero,add_zero] at eq
    · right; rwa [neg,mul_neg_one,←sub_eq_add_neg] at eq
  have pt (t:ZMod p) : (h t)^2-(2*r-n)*h t+r*(r-n)=0 := by rcases pair t with a|a <;> rw [a] <;> ring
  have total := sum_congr (s₁:=univ) rfl (fun t _=>pt t)
  simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_zero] at total
  change energy h-(2*r-n)*mass h+r*((p:ℤ)*r-(p:ℤ)*n)=0 at total
  rw [eh,mh,mul_zero,sub_zero] at total
  have roots : (r-s)*(r-E)=0 := by
    apply mul_left_cancel₀ pp.ne'
    rw [mul_zero]
    calc
      _=n*E+r*((p:ℤ)*r-(p:ℤ)*n) := by dsimp only [n,E]; ring
      _=0 := total
  have witness : ∃t:ZMod p,h t=E∨h t= -E := by
    by_contra! wrong
    rcases mul_eq_zero.mp roots with rs|re
    · have c (t:ZMod p) : h t=s := by
        have a:=pair t; have b:=wrong t; dsimp only [E] at b; omega
      have bad : mass h=(p:ℤ)*s := by simp [mass,c,ZMod.card]
      change 0<(p:ℤ)*s at nn
      omega
    · have c (t:ZMod p) : h t= -s := by
        have a:=pair t; have b:=wrong t; dsimp only [E] at re b; omega
      have bad : mass h= -((p:ℤ)*s) := by simp [mass,c,ZMod.card]
      change 0<(p:ℤ)*s at nn
      omega
  obtain ⟨t,pos|neg⟩:=witness
  · exact ⟨t,1,Or.inl rfl,signed_match_pointwise u w eu' ew' t 1 (by decide) (by simpa [h] using pos)⟩
  · exact ⟨t,-1,Or.inr rfl,signed_match_pointwise u w eu' ew' t (-1) (by decide) (by simpa [h] using neg)⟩

#print axioms uniform_signed_match

end Signed39.Template

