module

public import Quantum.SpectrumInduction
public import Quantum.SmallSix
public import Quantum.SmallSeven
public import Quantum.SmallEight
public import Quantum.NineClassification
public import Quantum.SmallTen
public import Quantum.OrderElevenSpectrum

/-! Complete classification of projective cardinalities for complex quantum
    Latin squares of every order at least six. -/
@[expose] public section
namespace QuantumCertificate

private theorem base (m : ℕ) (lo : 6 ≤ m) (hi : m < 12) : Good m := by
  interval_cases m
  · exact SmallSix.good
  · exact SmallSeven.good
  · exact SmallEight.good
  · exact fun c l u e => (NineSpectrum.spectrum c).mpr ⟨l,u,e⟩
  · exact SmallTen.good
  · exact fun c l u e => (OrderEleven.spectrum c).mpr ⟨l,u,e⟩

/-- For every order n ≥ 6, the possible numbers of complex rays are precisely
    the integers from n through n² with the sole exception of n+1. -/
theorem spectrum (n c : ℕ) (hn : 6 ≤ n) : Realized n c ↔ n ≤ c ∧ c ≤ n^2 ∧ c ≠ n+1 := by
  simpa only [pow_two] using spectrum_above_six_of_base base n hn c

#print axioms spectrum
end QuantumCertificate
