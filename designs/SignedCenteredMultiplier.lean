import SignedUniformMatch

namespace Signed39.Template

open Finset Contraction

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

def timesEquiv (a : ZMod p) (nz : a≠0) : ZMod p ≃+ ZMod p where
  toFun x:=a*x
  invFun x:=a⁻¹*x
  left_inv x:=by simp only [←mul_assoc,inv_mul_cancel₀ nz,one_mul]
  right_inv x:=by simp only [←mul_assoc,mul_inv_cancel₀ nz,one_mul]
  map_add' x y:=by ring

theorem centered_power_match (u : ZMod p → ℤ) (j a b : ℕ) (bp : 0<b)
    (E : ZMod p ≃+ ZMod p) (act : ∀x:ZMod p,q^a • x=E x) (identity : ∀x:ZMod p,q^b • x=x)
    (cop : IsCoprime (p:ℤ) ((q:ℤ)^j)) (mu : mass u=0)
    (flat : ∀t,corr u t=(if t=0 then (p:ℤ)*(q:ℤ)^j else 0)-(q:ℤ)^j) :
    ∃(t:ZMod p)(sg:ℤ),(sg=1∨sg= -1) ∧ ∀x,u (E.symm x)=sg*u (x-t) := by
  let s:ℤ:=(q:ℤ)^j
  let v:=fun x=>u (E.symm x)
  have sm : 0<s := pow_pos (by exact_mod_cast (Fact.out : q.Prime).pos) j
  have vm : mass v=0 := (equiv_mass E.symm.toEquiv u).trans mu
  have eu : energy u=(p:ℤ)*s-s := by rw [energy_zero,flat]; simp [s]
  have ev : energy v=energy u := Fintype.sum_equiv E.symm.toEquiv _ _ (fun _=>rfl)
  have vf (t) : corr v t=(if t=0 then (p:ℤ)*s else 0)-s := by
    have eq : corr v t=corr u (E.symm t) := Fintype.sum_equiv E.symm.toEquiv _ _ (fun x=>by dsimp [v]; rw [map_add])
    rw [eq,flat]; simp only [map_eq_zero_iff _ E.symm.injective]; rfl
  have cp (A:ZMod p→ℤ) (h:∀t,corr A t=(if t=0 then (p:ℤ)*s else 0)-s) (t:ZMod p) :
      ModularSupport.rcorr (fun x=>(A x:ZMod p)) t= -(s:ZMod p) := by
    have e:=congrArg (fun z:ℤ=>(z:ZMod p)) (h t)
    change (↑(∑i,A i*A (i+t)):ZMod p)=_ at e
    simpa only [ModularSupport.rcorr,Int.cast_sum,Int.cast_mul,Int.cast_sub,Int.cast_ite,Int.cast_zero,
      Int.cast_natCast,ZMod.natCast_self,zero_mul,ite_self,zero_sub] using e
  have pm (t) : (p:ℤ)∣matched v u t-matched v u 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [Int.cast_sub,sub_eq_zero]
    simp only [matched,Int.cast_sum,Int.cast_mul,sub_eq_add_neg,neg_zero,add_zero]
    exact ModularSupport.cross_constant _ _ _ _ (cp v vf) (cp u flat) (-t)
  have dz (t) : s∣corr u t := by
    rw [flat]; change s∣(if t=0 then (p:ℤ)*s else 0)-s
    apply dvd_sub _ (dvd_refl _)
    split <;> simp
  have qm (t) : s∣matched v u t := prime_power_match_zero u E j a b bp act identity dz t
  exact uniform_signed_match v u s sm vm (ev.trans eu) eu flat (fun t=>cop.mul_dvd (pm t) (dvd_sub (qm t) (qm 0)))

#print axioms centered_power_match

end Signed39.Template

