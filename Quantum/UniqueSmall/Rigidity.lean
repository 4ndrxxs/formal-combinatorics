module
public import Quantum.UniqueSmall.Family
public import Quantum.SudokuClueRigidity

@[expose] public section
namespace SudokuTrade
theorem inequivalent_of_nine_le {n : ℕ} (hn : 9≤n) : UniqueQuantumCounterexample n := by
  haveI : NeZero n := ⟨by omega⟩
  exact SudokuLocus.many_iff_inequivalent.mp (unique_many_of_nine_le hn)
#print axioms inequivalent_of_nine_le
end SudokuTrade
