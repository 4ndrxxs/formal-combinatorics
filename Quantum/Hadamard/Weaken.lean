import Quantum.Hadamard.Basic

namespace HadamardMod

theorem at_weaker_modulus {m M n : ℕ} (dv : m∣M) (H : AtOrder M n) : AtOrder m n := by
  obtain ⟨A,g⟩ := H
  let f := ZMod.castHom dv (ZMod m)
  refine ⟨fun i j => f (A i j),⟨?_,?_⟩⟩
  · intro i j
    rcases g.sign i j with h|h <;> simp [h,Sign]
  · intro i k ne
    simpa using congrArg f (g.ortho i k ne)

end HadamardMod
