import Quantum.Hadamard.ArithmeticSelfDualGauss

/-! An explicit base-p digit summation gives G(p²r)=p G(r) for all
positive r and odd primes p. No square-root sign convention is used. -/
noncomputable section
namespace Hadamard.Gauss
open Finset Complex

def phase (m x:ℕ) : ℂ := Complex.exp (2*Real.pi*I*x/m)
def sumSquares (m:ℕ) : ℂ := ∑ x:Fin m, phase m (x.val^2)

private theorem phase_char {m:ℕ} [NeZero m] (x:ℕ) :
    phase m x=ZMod.stdAddChar (x:ZMod m) := by
  have h := ZMod.stdAddChar_coe (N:=m) (x:ℤ)
  simpa [phase] using h.symm

private theorem phase_scale {a b:ℕ} (ap:0<a) (bp:0<b) (x:ℕ) :
    phase (b*a) (a*x)=phase b x := by
  unfold phase
  congr 1
  push_cast
  have ha : (a:ℂ)≠0 := by exact_mod_cast ap.ne'
  have hb : (b:ℂ)≠0 := by exact_mod_cast bp.ne'
  field_simp

private def finiteResidues (m:ℕ) [NeZero m] : Fin m ≃ ZMod m where
  toFun a := a.val
  invFun x := ⟨x.val,ZMod.val_lt x⟩
  left_inv a := Fin.ext (by simp [ZMod.val_natCast,Nat.mod_eq_of_lt a.isLt])
  right_inv x := ZMod.natCast_zmod_val x

theorem sumSquares_eq {m:ℕ} [NeZero m] :
    sumSquares m=∑ x:ZMod m,ZMod.stdAddChar (x*x) := by
  apply Eq.trans _ (Equiv.sum_comp (finiteResidues m) (fun t:ZMod m => ZMod.stdAddChar (t*t)))
  unfold sumSquares
  apply sum_congr rfl; intro i _
  rw [phase_char,Nat.cast_pow,pow_two]
  rfl

private theorem split (a b:ℕ) (f:Fin (a*b) → ℂ) :
    (∑ i,f i)=∑ j:Fin a,∑ k:Fin b,f (finProdFinEquiv (j,k)) := by
  exact (Equiv.sum_comp (finProdFinEquiv : Fin a×Fin b≃_) f).symm.trans
    (Fintype.sum_prod_type (fun e:Fin a×Fin b => f (finProdFinEquiv e)))

theorem digit_reduction {p r:ℕ} (pp:p.Prime) (po:2 < p) (rp:0 < r) :
    sumSquares (p*(r*p))=p*sumSquares r := by
  classical
  let : Fact p.Prime := ⟨pp⟩
  let N := p*(r*p)
  let : NeZero r := ⟨rp.ne'⟩
  let : NeZero N := ⟨(Nat.mul_pos pp.pos (Nat.mul_pos rp pp.pos)).ne'⟩
  have modN : (p:ZMod N)*((r:ZMod N)*p)=0 := by
    simpa only [N,Nat.cast_mul] using (ZMod.natCast_self (p*(r*p)))
  have expn (k j i:ℕ) :
      phase N ((i+p*j+(r*p)*k)^2)=phase N ((i+p*j)^2)*phase p (2*i*k) := by
    rw [←phase_scale (a:=r*p) (b:=p) (Nat.mul_pos rp pp.pos) pp.pos (2*i*k)]
    change phase N ((i+p*j+(r*p)*k)^2)=phase N ((i+p*j)^2)*phase N ((r*p)*(2*i*k))
    simp only [phase_char,←AddChar.map_add_eq_mul]
    congr 1
    push_cast
    linear_combination (2*(j:ZMod N)*k+(r:ZMod N)*k^2)*modN
  have orth (i:Fin p) : (∑ k:Fin p,phase p (2*i.val*k.val))=if i.val=0 then (p:ℂ) else 0 := by
    have ch := AddChar.sum_mulShift ((2:ZMod p)*(i.val:ZMod p)) (ZMod.isPrimitive_stdAddChar p)
    have et := Equiv.sum_comp (finiteResidues p) (fun t:ZMod p => ZMod.stdAddChar (t*((2:ZMod p)*(i.val:ZMod p))))
    have iz : (i.val:ZMod p)=0 ↔ i.val=0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact ⟨fun h => (Nat.eq_zero_of_dvd_of_lt h i.isLt),fun h => by simp [h]⟩
    have two : (2:ZMod p)≠0 := by
      exact (show IsUnit (2:ZMod p) by
        simpa using (ZMod.isUnit_iff_coprime 2 p).mpr (Hadamard.Arithmetic.two_coprime_prime pp po)).ne_zero
    calc
      _ = ∑ k:Fin p,ZMod.stdAddChar (finiteResidues p k*((2:ZMod p)*(i.val:ZMod p))) := by
        apply sum_congr rfl; intro k _
        rw [phase_char]
        congr 1
        change ((2*i.val*k.val:ℕ):ZMod p)=(k.val:ZMod p)*((2:ZMod p)*(i.val:ZMod p))
        push_cast; ring
      _ = _ := by
        by_cases h:i.val=0 <;> simpa [ZMod.card,mul_eq_zero,two,iz,h] using et.trans ch
  have small (j:Fin r) : phase N ((p*j.val)^2)=phase r (j.val^2) := by
    rw [show N=r*(p*p) by dsimp [N];ring,
      show (p*j.val)^2=(p*p)*j.val^2 by ring]
    exact phase_scale (Nat.mul_pos pp.pos pp.pos) rp _
  change sumSquares N=p*sumSquares r
  calc
    _ = ∑ k:Fin p,∑ j:Fin r,∑ i:Fin p,phase N ((i.val+p*j.val+(r*p)*k.val)^2) := by
      unfold sumSquares
      rw [split p (r*p)]
      apply sum_congr rfl; intro k _
      rw [split r p]
      rfl
    _ = ∑ j:Fin r,∑ i:Fin p,phase N ((i.val+p*j.val)^2)*(∑ k:Fin p,phase p (2*i.val*k.val)) := by
      simp_rw [expn]
      rw [sum_comm]
      apply sum_congr rfl; intro j _
      rw [sum_comm]
      simp only [mul_sum]
    _ = ∑ j:Fin r,(p:ℂ)*phase r (j.val^2) := by
      apply sum_congr rfl; intro j _
      simp only [orth,mul_ite,mul_zero,Fin.val_eq_zero_iff]
      simp [small,mul_comm (p:ℂ)]
    _ = _ := by simp [sumSquares,mul_sum]

#print axioms digit_reduction
end Hadamard.Gauss
