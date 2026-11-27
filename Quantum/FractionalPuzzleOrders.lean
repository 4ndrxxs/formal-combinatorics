module
public import Quantum.FractionalPuzzleQuotient
public import Quantum.FractionalImpossible9
public import Quantum.FractionalImpossible11
public import Quantum.FractionalImpossible13
public import Quantum.FractionalPadded5
public import Quantum.FractionalPadded6
public import Quantum.FractionalPadded8
public import Quantum.FractionalPadded10
public import Quantum.FractionalPadded12
public import Quantum.FractionalTwo.Physical

/-! The first Nechita–Pillet conjecture holds for block side two, fails at
every block side of five or greater. -/
@[expose] public section
namespace SudokuEmbedding
open QuantumSudoku PartialSudoku

theorem counterexamples (n : ℕ) (hn : 14≤n ∨ (7≤n ∧ Odd n)) :
    ∃ (p : Puzzle n) (v : Grid (Fin n)),QuantumCompletes p v ∧ ¬∃ g,ClassicalCompletes p g := by
  by_cases h : 14≤n
  · exact counterexamples_large _ h
  · obtain ⟨lo,⟨j,hj⟩⟩ := hn.resolve_left h
    have cases : n=7 ∨ n=9 ∨ n=11 ∨ n=13 := by omega
    rcases cases with rfl|rfl|rfl|rfl
    · exact ImpossibleSudoku7.counterexample
    · exact ImpossibleSudoku9.counterexample
    · exact ImpossibleSudoku11.counterexample
    · exact ImpossibleSudoku13.counterexample

theorem counterexamples_from_seven (n : ℕ) (hn : 7≤n) :
    ∃ (p : Puzzle n) (v : Grid (Fin n)),QuantumCompletes p v ∧ ¬∃ g,ClassicalCompletes p g := by
  by_cases h : 14≤n ∨ (7≤n ∧ Odd n)
  · exact counterexamples n h
  · have nh : ¬Odd n := fun ho => h (Or.inr ⟨hn,ho⟩)
    have lo : n<14 := by omega
    have even : Even n := Nat.not_odd_iff_even.mp nh
    obtain ⟨k,hk⟩ := even
    have e : n=8 ∨ n=10 ∨ n=12 := by omega
    rcases e with rfl|rfl|rfl
    · exact ImpossiblePadded8.counterexample
    · exact ImpossiblePadded10.counterexample
    · exact ImpossiblePadded12.counterexample

theorem counterexamples_from_five (n : ℕ) (hn : 5≤n) :
    ∃ (p : Puzzle n) (v : Grid (Fin n)),QuantumCompletes p v ∧ ¬∃ g,ClassicalCompletes p g := by
  by_cases h : 7≤n
  · exact counterexamples_from_seven n h
  · have e : n=5 ∨ n=6 := by omega
    rcases e with rfl|rfl
    · exact ImpossiblePadded5.counterexample
    · exact ImpossiblePadded6.counterexample

#print axioms counterexamples_from_five
#print axioms counterexamples_from_seven
#print axioms counterexamples
end SudokuEmbedding
