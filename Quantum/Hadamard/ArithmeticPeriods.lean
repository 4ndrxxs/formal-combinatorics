import Quantum.Hadamard.ArithmeticOneStep

/-! Euler's theorem gives a common period for the field-size powers and
their geometric sum at every positive modulus. -/
namespace HadamardMod
open Hadamard.PG Finset

theorem geom_period {M q : ℕ} (hp : 0 < M) (cop : q.Coprime M) :
    ∃ d : ℕ, (geom q (d+2):ZMod M)=0 ∧ (q:ZMod M)^(d+2)=1 := by
  let e := M.totient
  have ep : 0 < e := Nat.totient_pos.mpr hp
  have inv : (q:ZMod M)^e=1 := by
    simpa [e] using (ZMod.natCast_eq_natCast_iff _ _ M).mpr (Nat.ModEq.pow_totient cop)
  have plus (a b:ℕ) : geom q (a+b)=geom q a+q^a*geom q b := by
    simp [geom,sum_range_add,pow_add,mul_sum]
  have period (t : ℕ) : (geom q (e*t):ZMod M)=(t:ZMod M)*(geom q e:ZMod M) := by
    induction t with
    | zero => simp [geom]
    | succ t IH =>
      rw [Nat.mul_succ,plus,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,pow_mul,inv,one_pow,one_mul,IH]
      push_cast
      ring
  have d2 : e*(2*M)-2+2=e*(2*M) := by
    have : 2≤e*(2*M) := by nlinarith
    omega
  refine ⟨e*(2*M)-2,?_,?_⟩
  · rw [d2,period]
    simp
  · rw [d2,pow_mul,inv,one_pow]

end HadamardMod
