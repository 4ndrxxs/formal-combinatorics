import SignedMultiplierShapes
import SignedMultiplierOrbits

namespace Signed39.Template

open Finset Contraction

variable {p q:ℕ} [Fact p.Prime] [Fact q.Prime]

theorem centered_anchor_residue (j e d:ℕ) (u:ZMod p→ℤ) (W:ZMod p→ℤ) (mu:mass u=0)
    (flat:∀t,corr u t=(if t=0 then (p:ℤ)*(q:ℤ)^j else 0)-(q:ℤ)^j)
    (nz:(q:ZMod p)≠0) (na:(q:ZMod p)≠1) (ep:0<e) (iden:(q:ZMod p)^e=1)
    (cop:IsCoprime (p:ℤ) ((q:ℤ)^j))
    (levels:∀x:ZMod p,(d:ℤ)∣(if x=0 then (0:ℤ) else 1)+W ((q:ZMod p)^2*x)-W x) :
    ∃i:ZMod p,(d:ℤ)∣u i := by
  let E:=timesEquiv (q:ZMod p) nz
  have act (x:ZMod p) : q^1 • x=E x := by simp [E,timesEquiv,nsmul_eq_mul]
  have id (x:ZMod p) : q^e • x=x := by rw [nsmul_eq_mul,Nat.cast_pow,iden,one_mul]
  obtain ⟨base,fix⟩:=square_multiplier_fixed u (q:ZMod p) nz na (centered_power_match u j 1 e ep E act id cop mu flat)
  let v:=fun i=>u (i+base)
  let T:=timesEquiv ((q:ZMod p)^2) (pow_ne_zero 2 nz)
  have got:=orbit_mass_dvd T.toEquiv v W d 0 fix levels
  have mv:mass v=0:=(sum_translate u base).trans mu
  rw [mv,zero_sub,dvd_neg] at got
  exact ⟨base,by simpa [v] using got⟩

#print axioms centered_anchor_residue

end Signed39.Template

