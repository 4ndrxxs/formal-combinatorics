module
public import Quantum.Sudoku

/-! A three-index array with a basis on every coordinate slice lifts to
a quantum Sudoku via the sum of its band and stack indices. -/
@[expose] public section
noncomputable section
namespace SudokuCyclicLift
open QuantumSudoku

variable {I : Type*} [Fintype I] [DecidableEq I] [AddCommGroup I]

def board (G : I→I→I→H I) : Grid I := fun r c => G r.2 c.2 (r.1+c.1)

theorem valid (G : I→I→I→H I)
    (hr : ∀ (r : I) (p q : Index I),
      inner ℂ (G r p.1 p.2) (G r q.1 q.2)=if p=q then 1 else 0)
    (hc : ∀ (c : I) (p q : Index I),
      inner ℂ (G p.1 c p.2) (G q.1 c q.2)=if p=q then 1 else 0)
    (hb : ∀ (t : I) (p q : Index I),
      inner ℂ (G p.1 p.2 t) (G q.1 q.2 t)=if p=q then 1 else 0) : Valid (board G) := by
  constructor
  · rintro ⟨x,r⟩
    apply basis_of_gram
    rintro ⟨y,c⟩ ⟨z,b⟩
    simpa [board,and_comm] using hr r (c,x+y) (b,x+z)
  · rintro ⟨y,c⟩
    apply basis_of_gram
    rintro ⟨x,r⟩ ⟨z,b⟩
    simpa [board,and_comm] using hc c (r,x+y) (b,z+y)
  · intro x y
    apply basis_of_gram
    rintro ⟨r,c⟩ ⟨s,b⟩
    exact hb (x+y) (r,c) (s,b)

end SudokuCyclicLift
