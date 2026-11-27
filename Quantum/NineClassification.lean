module

public import Quantum.Bounds
public import Quantum.NineSpectrum.Complete

@[expose] public section
namespace NineSpectrum
open QuantumCertificate

/-- All possible projective cardinalities of order-nine quantum Latin squares. -/
theorem spectrum (c : ℕ) : Realized 9 c ↔ 9 ≤ c ∧ c ≤ 81 ∧ c ≠ 10 :=
  ⟨fun h => h.bounds, fun ⟨hl,hu,he⟩ => positive c hl hu he⟩

#print axioms spectrum
end NineSpectrum
