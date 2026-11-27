import Quantum.Hadamard.AffineSeeds
import Quantum.Hadamard.ConferenceSeed
import Quantum.Hadamard.ArithmeticLinear
import Quantum.Hadamard.PaleyKuperberg

/-! The eventual spectrum of modular Hadamard matrices at every odd prime.
Quadratic squares include zero. The finite exceptional set may depend on the prime. -/
noncomputable section
namespace HadamardMod
open Hadamard.Arithmetic

private theorem admissible_spec {p n : ℕ} :
    KuperbergAdmissible p n ↔ Even n ∨ IsSquare (n:ZMod p) := by
  simp only [KuperbergAdmissible,Nat.even_iff,hasRoot_iff_isSquare]

/-- At all sufficiently large orders for a fixed odd prime, the necessary
parity-or-square condition is also sufficient. -/
theorem kuperberg {p : ℕ} (prime : p.Prime) (odd : 2<p) :
    ∃ B : ℕ, ∀ n ≥ B, AtOrder p n ↔ Even n ∨ IsSquare (n:ZMod p) := by
  letI : Fact p.Prime := ⟨prime⟩
  rcases prime_residue_bridge odd with eight|three|two
  · obtain ⟨x,u,ns,identity⟩ := linear_twist eight
    have seed := conference_nonsquare_seed odd ns identity
    obtain ⟨B,h⟩ := kuperberg_given_twice_odd_seed prime odd seed
    exact ⟨B,fun n hn => (h n hn).trans admissible_spec⟩
  · exact kuperberg_three_mod_four prime three
  · obtain ⟨B,h⟩ := kuperberg_given_twice_odd_seed prime odd (two_nonsquare_seed two)
    exact ⟨B,fun n hn => (h n hn).trans admissible_spec⟩

/-- Integer sign matrices and literal divisibility of every entry of the
Gram matrix difference. This is Conjecture 5.1 with zero counted as a square. -/
theorem kuperberg_integer {p : ℕ} (prime : p.Prime) (odd : 2<p) :
    ∃ B : ℕ, ∀ n ≥ B, IntegralSolution p n ↔ Even n ∨ IsSquare (n:ZMod p) := by
  letI : Fact p.Prime := ⟨prime⟩
  obtain ⟨B,h⟩ := kuperberg prime odd
  exact ⟨B,fun n hn => ⟨prime_integral_necessary,fun a => integer_gram ((h n hn).mpr a)⟩⟩

#print axioms kuperberg
#print axioms kuperberg_integer
end HadamardMod
