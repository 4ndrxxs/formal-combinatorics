module
public import Quantum.UniqueSmall.Rigidity
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Exact cardinalities for the space of projective solutions of one puzzle.
The ambient finite complex grid gives the upper bound even after quotienting. -/
@[expose] public section
noncomputable section
namespace SudokuLocus
open Cardinal QuantumSudoku PartialSudoku SudokuEmbedding FractionalLayouts

theorem mk_circle : Cardinal.mk Circle=continuum :=
  (mk_congr Circle.argEquiv).trans (mk_Ioc_real (by linarith [Real.pi_pos]))

private theorem arrow_bound {A B : Type} [Countable A] (h : Cardinal.mk B≤continuum) :
    Cardinal.mk (A→B)≤continuum := by
  rw [mk_arrow,lift_id,lift_id]
  exact (power_le_power_right h).trans
    ((power_le_power_left continuum_ne_zero mk_le_aleph0).trans_eq continuum_power_aleph0)

theorem quantum_card_bound {n : ℕ} (p : Puzzle n) : Cardinal.mk (QSolutions p)≤continuum := by
  have linear : Cardinal.mk (H (Fin n))≤Cardinal.mk (Sites n→ℂ) :=
    mk_le_of_injective (f:=fun w : H (Fin n) => fun i => w i) (fun _ _ eq => by ext j; exact congrFun eq j)
  have hb := linear.trans (arrow_bound mk_complex.le)
  exact mk_quotient_le.trans ((mk_subtype_le _).trans (arrow_bound (arrow_bound hb)))

theorem card_eq_continuum {n : ℕ} {p : Puzzle n} (h : Nonempty (Circle ↪ QSolutions p)) :
    Cardinal.mk (QSolutions p)=continuum := by
  obtain ⟨e⟩:=h
  exact (quantum_card_bound p).antisymm (mk_circle ▸ mk_le_of_injective e.injective)

theorem classical_or_exact_continuum {n : ℕ} [NeZero n] (p : Puzzle n) :
    Nonempty ({f : Solution n // ClassicalCompletes p f} ≃ QSolutions p) ∨
    Cardinal.mk (QSolutions p)=continuum := by
  rcases classical_or_circle p with h|h
  · exact Or.inl ⟨Equiv.ofBijective _ ⟨(classicalEmbedding p).injective,h⟩⟩
  · exact Or.inr (card_eq_continuum h)

theorem unique_exact_continuum_of_nine_le {n : ℕ} (hn : 9≤n) :
    ∃ p : Puzzle n, (∃! f,ClassicalCompletes p f) ∧
      (∃ v w : Grid (Fin n),QuantumCompletes p v ∧ QuantumCompletes p w ∧ ¬Equivalent v w) ∧
      Cardinal.mk (QSolutions p)=continuum := by
  obtain ⟨p,unique,inequivalent,many⟩:=SudokuTrade.inequivalent_of_nine_le hn
  exact ⟨p,unique,inequivalent,card_eq_continuum many⟩

#print axioms classical_or_exact_continuum
#print axioms unique_exact_continuum_of_nine_le
end SudokuLocus
