import Quantum.Hadamard.Lex
import Quantum.Hadamard.Paley

/-! Reduction of the integral Paley character matrix to a skew modular core. -/

noncomputable section
namespace HadamardMod

/-- Every prime congruent to three modulo four supplies a skew core for each modulus. -/
def paleySkew (m q : ℕ) [Fact q.Prime] (hq : q % 4 = 3) : SkewCore m (ZMod q) where
  entry i j := (Hadamard.Paley.Q q i j : ZMod m)
  diag i := by simp
  sign i j ne := by
    rcases Hadamard.Paley.Q_sign_of_ne q ne with h|h <;> simp [h,Sign]
  skew i j := by
    rw [Hadamard.Paley.Q_skew q hq i j, Int.cast_neg]
  row i := by
    simpa only [Int.cast_sum,Int.cast_zero] using congrArg (fun z : ℤ => (z : ZMod m))
      (Hadamard.Paley.Q_row_sum q hq i)
  gram i k := by
    have h := congrArg (fun z : ℤ => (z : ZMod m)) (Hadamard.Paley.Q_gram q hq i k)
    by_cases e : i=k <;>
      simpa [e, Int.cast_sum, Int.cast_mul, Int.cast_sub, ZMod.card] using h

#print axioms paleySkew
end HadamardMod

