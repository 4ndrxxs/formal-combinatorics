import Quantum.Hadamard.Asymptotic
import Quantum.Hadamard.PaleyParity
import Quantum.Hadamard.PaleyNecessity

/-! Kuperberg's asymptotic existence conjecture for every prime three modulo four. -/
noncomputable section
namespace HadamardMod

/-- Eventual existence holds at exactly the allowed orders for every prime
congruent to three modulo four. The cutoff may depend on the prime. -/
theorem kuperberg_three_mod_four {p : ℕ} (prime : p.Prime) (hp : p%4=3) :
    ∃ B : ℕ, ∀ n : ℕ, n≥B →
      (AtOrder p n ↔ Even n ∨ IsSquare (n:ZMod p)) := by
  let : Fact p.Prime := ⟨prime⟩
  obtain ⟨B,hB⟩ := Hadamard.PG.parity_bridge_three_mod_four hp
    (all_large_four_mod_prime prime (by omega))
  exact ⟨B,fun n large => ⟨fun h => prime_integral_necessary (integer_gram h),hB n large⟩⟩

/-- The sign condition and the divisibility of every entry of the integral Gram
matrix difference are explicit in `IntegralSolution`. -/
theorem kuperberg_three_mod_four_integer {p : ℕ} (prime : p.Prime) (hp : p%4=3) :
    ∃ B : ℕ, ∀ n : ℕ, n≥B →
      (IntegralSolution p n ↔ Even n ∨ IsSquare (n:ZMod p)) := by
  let : Fact p.Prime := ⟨prime⟩
  obtain ⟨B,hB⟩ := kuperberg_three_mod_four prime hp
  exact ⟨B,fun n large => ⟨prime_integral_necessary,fun h => integer_gram ((hB n large).mpr h)⟩⟩

#print axioms kuperberg_three_mod_four
#print axioms kuperberg_three_mod_four_integer
end HadamardMod

