import SignedReducedQuotient

namespace Signed39.Contraction

open Finset

variable {m:ℕ} [NeZero m]

private def firstMoment (u:ZMod m→ℤ) : ZMod m := ∑x,x*(u x:ZMod m)

theorem fixed_weighted_translate (u:ZMod m→ℤ) (E:ZMod m≃+ZMod m) (t:ℕ) (a b:ℤ)
    (scale:∀x,E x=(t:ZMod m)*x) (bez:(a:ZMod m)*(mass u:ZMod m)+(b:ZMod m)*((t:ZMod m)-1)=1)
    (g:ZMod m) (matchEq:∀x,u (E.symm x)=u (x-g)) :
    ∃w:ZMod m→ℤ,mass w=mass u ∧ (∀x,w ((t:ZMod m)*x)=w x) ∧ ∀z,corr w z=corr u z := by
  let M:ZMod m:=mass u
  let X:=firstMoment u
  have lhs : firstMoment (fun x=>u (E.symm x))=(t:ZMod m)*X := by
    change (∑x,x*(u (E.symm x):ZMod m))=(t:ZMod m)*∑x,x*(u x:ZMod m)
    rw [mul_sum]
    apply Fintype.sum_equiv E.symm.toEquiv
    intro x
    change x*(u (E.symm x):ZMod m)=(t:ZMod m)*(E.symm x*(u (E.symm x):ZMod m))
    rw [←mul_assoc,←scale,E.apply_symm_apply]
  have rhs : firstMoment (fun x=>u (x-g))=X+g*M := by
    calc
      _=∑x:ZMod m,(x+g)*(u x:ZMod m) := Fintype.sum_equiv (Equiv.addRight (-g)) _ _
        (fun x=>by simp [sub_eq_add_neg])
      _=_ := by simp [firstMoment,X,M,mass,add_mul,sum_add_distrib,←mul_sum]
  have eq:(t:ZMod m)*X=X+g*M := lhs.symm.trans ((congrArg firstMoment (funext matchEq)).trans rhs)
  let base:ZMod m:=a*X+b*g
  have solve:((t:ZMod m)-1)*base=g := by
    dsimp only [base]; change (a:ZMod m)*M+(b:ZMod m)*((t:ZMod m)-1)=1 at bez
    linear_combination (a:ZMod m)*eq+g*bez
  let w:=fun x=>u (x+base)
  refine ⟨w,sum_translate _ _,fun x=>?_,fun z=>?_⟩
  · have tr:=matchEq (E (x+base))
    rw [E.symm_apply_apply,scale] at tr
    change u ((t:ZMod m)*x+base)=u (x+base)
    rw [show (t:ZMod m)*(x+base)-g=(t:ZMod m)*x+base by linear_combination solve] at tr; exact tr.symm
  · unfold corr
    exact Fintype.sum_equiv (Equiv.addRight base) _ _ (fun x=>by dsimp [w]; rw [show x+z+base=x+base+z by abel])

theorem fixed_flat_quotient (u:ZMod m→ℤ) (n t inv:ℕ) (l A a b:ℤ)
    (positive:0<n) (flat:∀z,corr u z=(if z=0 then (n:ℤ) else 0)+l) (ms:mass u=A)
    (inverse:t*inv ≡ 1 [MOD m]) (bez:(a:ZMod m)*(A:ZMod m)+(b:ZMod m)*((t:ZMod m)-1)=1)
    (L:List AuxPower) (good:compatibleFactors m t n L) (prod:factorProduct L=n) :
    ∃w:ZMod m→ℤ,mass w=A ∧ (∀x,w ((t:ZMod m)*x)=w x) ∧
       ∀z,corr w z=(if z=0 then (n:ℤ) else 0)+l := by
  let E:=scalarPerm (H:=ZMod m) t inv (by simpa using inverse)
  have act (x:ZMod m) : t • x=E x:=rfl
  have all (x:ZMod m) : (n:ℤ)∣matched (fun y=>u (E.symm y)) u x-l :=
    prod ▸ all_aux_dvd u m t n l flat E (ZMod.card m) act L good x
  obtain ⟨g,eq⟩:=integral_match_translation u n l (by exact_mod_cast positive) flat E all
  obtain ⟨w,mw,fix,fw⟩:=fixed_weighted_translate u E t a b (fun x=>(act x).symm.trans (nsmul_eq_mul t x))
    (ms ▸ bez) g eq
  exact ⟨w,mw.trans ms,fix,fun z=>(fw z).trans (flat z)⟩

#print axioms fixed_weighted_translate
#print axioms fixed_flat_quotient

end Signed39.Contraction
