module
public import Quantum.SudokuTradeCertificate
public import Quantum.SudokuTradeWitness
public import Quantum.SudokuQuantumContinuum

/-! Classical uniqueness, two unitarily inequivalent completions, and a full
circle of distinct quantum completions in the original rank-one formulation. -/
@[expose] public section
noncomputable section
namespace SudokuTrade
open QuantumSudoku FractionalLayouts SudokuEmbedding

def UniqueQuantumCounterexample (n : ℕ) : Prop :=
  ∃ p : Puzzle n, (∃! f,PartialSudoku.ClassicalCompletes p f) ∧
    (∃ v w : Grid (Fin n), PartialSudoku.QuantumCompletes p v ∧
      PartialSudoku.QuantumCompletes p w ∧ ¬Equivalent v w) ∧
    Nonempty (Circle ↪ QSolutions p)

def UniqueMany (n : ℕ) : Prop :=
  ∃ p : Puzzle n, (∃! f,PartialSudoku.ClassicalCompletes p f) ∧ Nonempty (Circle ↪ QSolutions p)

theorem UniqueQuantumCounterexample.many {n : ℕ} (h : UniqueQuantumCounterexample n) : UniqueMany n := by
  obtain ⟨p,unique,_,many⟩:=h
  exact ⟨p,unique,many⟩

theorem UniqueMany.enlarge {k n : ℕ} [NeZero k] (h : UniqueMany k) (hn : 2*k≤n) : UniqueMany n := by
  let L := SudokuSubsquare.ofOrders k n hn
  obtain ⟨p,⟨f,hf,unique⟩,⟨circle⟩⟩:=h
  refine ⟨SudokuEmbedding.puzzle L p,⟨insertSolution L f,classical_insert L hf,?_⟩,
    ⟨circle.trans (quantumEquiv L p).toEmbedding⟩⟩
  intro g hg
  have eq:=unique _ (classical_restrict L hg)
  rw [←eq]
  exact (insert_restrict L hg).symm

variable [C : Config] [L : Laws]
include L

theorem classical_iff (p : Pair → Pair → Option Pair) (f : Pair→Pair→Pair) :
    ClassicalCompletes p f ↔ PartialSudoku.ClassicalCompletes p f := by
  constructor
  · rintro ⟨⟨row,col',block⟩,clues⟩
    refine ⟨?_,clues⟩
    intro d k
    cases d with
    | row => exact row k
    | column => exact col' k
    | block => exact block k.1 k.2
  · rintro ⟨lines,clues⟩
    exact ⟨⟨lines .row,lines .column,fun x y => lines .block (x,y)⟩,clues⟩

theorem chart_counterexample {r u : I} {i j l : Color}
    (forced : ∀ g : Active, Good g → ∀ r i,g 0 r i=i) (hl : j≠l)
    (hj : num (ray r i) j≠(0,0)) (hk : num (ray r i) l≠(0,0))
    (hp : ray u i=refRay i) : UniqueQuantumCounterexample C.side := by
  refine ⟨puzzle,⟨baseline,(classical_iff _ _).mp baseline_completes,?_⟩,
    ⟨coordinateBoard,quantumBoard,coordinate_completes,quantum_completes,inequivalent hl hj hk hp⟩,
    ⟨SudokuContinuum.circleEmbedding (p := puzzle) (v := quantumBoard) quantum_completes
      (fun e => hl (axis_inj e)) (nonzero_coordinate hj) (nonzero_coordinate hk)⟩⟩
  intro f hf
  exact unique_of_forced forced ((classical_iff _ _).mpr hf)

#print axioms chart_counterexample
end SudokuTrade
