module
public import Quantum.Activated.Side005
public import Quantum.Activated.Side006
public import Quantum.Activated.Side007
public import Quantum.Activated.Side008

@[expose] public section
namespace Activated
open QuantumSudoku PartialSudoku SudokuEmbedding FractionalLayouts

theorem inequivalent_of_five_le {n : ℕ} (hn : 5≤n) : SudokuTrade.UniqueQuantumCounterexample n := by
  by_cases h : 9≤n
  · exact SudokuTrade.inequivalent_of_nine_le h
  have small : n≤8 := by omega
  interval_cases n
  · exact Side005.counterexample
  · exact Side006.counterexample
  · exact Side007.counterexample
  · exact Side008.counterexample

theorem unique_continuum_of_five_le {n : ℕ} (hn : 5≤n) :
    ∃ p : Puzzle n, (∃! f,ClassicalCompletes p f) ∧
      (∃ v w : Grid (Fin n),QuantumCompletes p v ∧ QuantumCompletes p w ∧ ¬Equivalent v w) ∧
      Cardinal.mk (QSolutions p)=Cardinal.continuum := by
  obtain ⟨p,one,two,many⟩:=inequivalent_of_five_le hn
  exact ⟨p,one,two,SudokuLocus.card_eq_continuum many⟩
#print axioms inequivalent_of_five_le
#print axioms unique_continuum_of_five_le
end Activated
