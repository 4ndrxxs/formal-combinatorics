import Quantum.Hadamard.FiniteFieldAffine
import Quantum.Hadamard.ArithmeticBase

/-! Prime-field specialization of the affine plane sign construction. -/
noncomputable section
namespace Hadamard.Affine
open HadamardMod
variable {p q : ℕ} [Fact q.Prime]

abbrev Point (q : ℕ) := ZMod q × ZMod q

private abbrev signEntry (p : ℕ) (T : Finset (ZMod q)) :=
  Hadamard.FiniteFieldAffine.signEntry p T

theorem affine_good (T : Finset (ZMod q)) (chosen : 2*(T.card:ZMod p)=(q:ZMod p)) :
    Good (signEntry p T) :=
  Hadamard.FiniteFieldAffine.affine_good T (by simpa using chosen)

theorem at_square_order (T : Finset (ZMod q)) (chosen : 2*(T.card:ZMod p)=(q:ZMod p)) :
    AtOrder p (q^2) := by
  simpa using Hadamard.FiniteFieldAffine.at_square_order T (by simpa using chosen)

#print axioms at_square_order
end Hadamard.Affine
