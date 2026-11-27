module
public import Quantum.UniqueSmall.Side009
public import Quantum.UniqueSmall.Side010
public import Quantum.UniqueSmall.Side011
public import Quantum.UniqueSmall.Side012
public import Quantum.UniqueSmall.Side013
public import Quantum.UniqueSmall.Side014
public import Quantum.UniqueSmall.Side015
public import Quantum.UniqueSmall.Side016
public import Quantum.UniqueSmall.Side017

@[expose] public section
namespace SudokuTrade

theorem unique_many_large {n : ℕ} (hn : 18≤n) : UniqueMany n :=
  Side009.counterexample.many.enlarge (by omega)

theorem unique_many_of_nine_le {n : ℕ} (hn : 9≤n) : UniqueMany n := by
  by_cases h : 18≤n
  · exact unique_many_large h
  have small : n≤17 := by omega
  interval_cases n
  · exact Side009.counterexample.many
  · exact Side010.counterexample.many
  · exact Side011.counterexample.many
  · exact Side012.counterexample.many
  · exact Side013.counterexample.many
  · exact Side014.counterexample.many
  · exact Side015.counterexample.many
  · exact Side016.counterexample.many
  · exact Side017.counterexample.many

#print axioms unique_many_large
#print axioms unique_many_of_nine_le
end SudokuTrade
