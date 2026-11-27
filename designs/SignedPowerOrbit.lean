import SignedShapeBudget

namespace Signed39.Shape

open Finset Contraction Template

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

theorem power_two_cover (j e d R : ℕ) (rep : ZMod p) (tag : ZMod p→Bool)
    (nz : (q:ZMod p)≠0) (na : (q:ZMod p)≠1) (ep : 0<e) (identity : (q:ZMod p)^e=1)
    (cop : IsCoprime (p:ℤ) ((q:ℤ)^j))
    (orbit : ∀i:ZMod p,i≠0 → ∃k:Fin p,((q:ZMod p)^2)^k.val*(if tag i then 1 else rep)=i)
    (first : (∑i:ZMod p,classWord tag (0:ℤ) 1 0 i)=d)
    (second : (∑i:ZMod p,classWord tag (0:ℤ) 0 1 i)=d)
    (bound : (p:ℤ)*(q:ℤ)^j-(q:ℤ)^j<((R:ℤ)+1)^2) (u : ZMod p→ℤ) (mu : mass u=0)
    (flat:∀t,corr u t=(if t=0 then (p:ℤ)*(q:ℤ)^j else 0)-(q:ℤ)^j) :
    ∃L∈twoForms d R ((p:ℤ)*(q:ℤ)^j-(q:ℤ)^j),∀F:ℤ→ℤ,(∑i,F (u i))=(L.map F).sum := by
  let E:=timesEquiv (q:ZMod p) nz
  have action (x:ZMod p) : q^1 • x=E x := by simp [E,timesEquiv,nsmul_eq_mul]
  have iden (x:ZMod p) : q^e • x=x := by rw [nsmul_eq_mul,Nat.cast_pow,identity,one_mul]
  obtain ⟨base,fix⟩:=square_multiplier_fixed u (q:ZMod p) nz na
    (centered_power_match u j 1 e ep E action iden cop mu flat)
  exact two_forms_complete u (q:ZMod p) rep tag d R _ base fix orbit first second mu
    (by rw [energy_zero,flat]; simp) bound

#print axioms power_two_cover

end Signed39.Shape

