module
public import Quantum.FractionalTwo.Unanchored
public import Quantum.FractionalPuzzleEmbedding
public import Quantum.FractionalBlockBell

/-! A genuine four-by-four quantum completion yields a nonnegative fractional
Sudoku by coordinate measurement. Deterministic weights at all printed cells
can be preserved by a single classical completion. -/
@[expose] public section
noncomputable section
namespace FractionalTwo
open Function Finset Complex QuantumSudoku PartialSudoku FractionalLayouts
open FractionalBlockBell (fromTiny toTiny lineNum tiny_line all_tiny_lines)
open scoped BigOperators

abbrev P := SudokuEmbedding.Puzzle 2
def FractionalCompletes (p : P) (t : A→ℝ) : Prop :=
  Fractional t ∧ ∀ r c j,p r c=some j → t (atom (number r,number c) (number j))=1

def vectorAt (v : Grid (Fin 2)) (s : S) := v (number.symm s.1) (number.symm s.2)
def measured (v : Grid (Fin 2)) (a : A) : ℝ := normSq (vectorAt v (loc a) (number.symm (digit a)))

theorem cell_total {v : Grid (Fin 2)} (hv : Valid v) (s : S) :
    ∑ d : Fin 4,normSq (vectorAt v s (number.symm d))=1 := by
  have unit : ‖vectorAt v s‖=1 := by
    obtain ⟨B,hB⟩ := hv.row (number.symm s.1)
    simpa only [hB,vectorAt] using B.orthonormal.1 (number.symm s.2)
  calc
    _=∑ j : Sites 2,normSq (vectorAt v s j) := Equiv.sum_comp number.symm _
    _=‖vectorAt v s‖^2 := by
      simpa [EuclideanSpace.inner_single_left,Complex.sq_norm] using
        (EuclideanSpace.basisFun (Sites 2) ℂ).sum_sq_norm_inner_right (vectorAt v s)
    _=1 := by simp [unit]

theorem line_total {v : Grid (Fin 2)} (hv : Valid v) (l : Fin 12) (j : Fin 4) :
    ∑ i : Fin 4,normSq (vectorAt v (FractionalBinary.line l i) (number.symm j))=1 := by
  obtain ⟨d,a,rfl⟩ := all_tiny_lines l
  let w := SudokuEmbedding.line d v a
  have h : BasisLine w := by
    cases d with
    | row => exact hv.row a
    | column => exact hv.column a
    | block => exact hv.block a.1 a.2
  obtain ⟨B,hB⟩ := h
  have gram := B.sum_sq_norm_inner_left (unitAxis (number.symm j))
  have oneline : (∑ s : Sites 2,normSq (w s (number.symm j)))=1 := by
    simpa [hB,unitAxis,EuclideanSpace.inner_single_left,Complex.sq_norm] using gram
  rw [←oneline,←Equiv.sum_comp number.symm (fun s => normSq (w s (number.symm j)))]
  apply sum_congr rfl
  intro i _
  have eq := tiny_line d a (number.symm i)
  rw [number.apply_symm_apply] at eq
  rw [←eq]
  simp [w,vectorAt,fromTiny,SudokuEmbedding.line]

theorem measured_fractional {v : Grid (Fin 2)} (hv : Valid v) : Fractional (measured v) := by
  refine ⟨fun a => normSq_nonneg _,fun u => ?_⟩
  by_cases hu : u.val<16
  · simpa only [house,hu,if_true,measured,loc_atom,digit_atom] using
      cell_total hv (Fin.ofNat 4 (u.val/4),Fin.ofNat 4 u.val)
  · simpa only [house,hu,if_false,measured,loc_atom,digit_atom] using
      line_total hv (Fin.ofNat 12 ((u.val-16)/4)) (Fin.ofNat 4 u.val)

theorem quantum_fractional {p : P} {v : Grid (Fin 2)} (hv : QuantumCompletes p v) :
    FractionalCompletes p (measured v) := by
  refine ⟨measured_fractional hv.1,?_⟩
  intro r c j h
  obtain ⟨z,hz⟩ := hv.2 _ _ _ h
  simp [measured,vectorAt,hz,unitAxis,PiLp.single_apply]

def answer (f : S→Fin 4) (r c : Sites 2) : Sites 2 := number.symm (f (number r,number c))

theorem answer_classical {p : P} {t : A→ℝ} {f : S→Fin 4} (ht : FractionalCompletes p t)
    (hf : Proper f) (agree : Agrees t f) : ClassicalCompletes p (answer f) := by
  constructor
  · intro d a
    apply Finite.injective_iff_bijective.mp
    intro i j h
    have h' := number.symm.injective h
    change f (fromTiny (arrange d (a,i)))=f (fromTiny (arrange d (a,j))) at h'
    rw [tiny_line,tiny_line] at h'
    exact number.injective (hf _ h')
  · intro r c j h
    have eq := agree _ (ht.2 r c j h)
    simpa [answer] using congrArg number.symm eq

theorem fractional_classical {p : P} {t : A→ℝ} (ht : FractionalCompletes p t) :
    ∃ f,ClassicalCompletes p f := by
  obtain ⟨f,hf,agree⟩ := integral_extension t ht.1
  exact ⟨answer f,answer_classical ht hf agree⟩

theorem classical_quantum {n : ℕ} [NeZero n] {p : SudokuEmbedding.Puzzle n}
    {f : SudokuEmbedding.Solution n} (hf : ClassicalCompletes p f) :
    QuantumCompletes p (fun r c => unitAxis (f r c)) := by
  have basis (d : Direction) (a : Sites n) : BasisLine (fun j =>
      unitAxis (f (arrange d (a,j)).1 (arrange d (a,j)).2)) := by
    apply basis_of_gram
    intro i j
    simp [SudokuEmbedding.axis_inner,(hf.1 d a).injective.eq_iff]
  exact ⟨⟨basis .row,basis .column,fun r c => basis .block (r,c)⟩,
    fun r c j h => ⟨1,by simp [hf.2 r c j h]⟩⟩

/-- Nechita–Pillet's first Sudoku conjecture holds for the physical 4-by-4 grid. -/
theorem conjecture_four_by_four (p : P) :
    (∃ v,QuantumCompletes p v) ↔ ∃ f,ClassicalCompletes p f := by
  exact ⟨fun ⟨_,hv⟩ => fractional_classical (quantum_fractional hv),
    fun ⟨_,hf⟩ => ⟨_,classical_quantum hf⟩⟩

/-- The same equivalence already holds at the ordinary linear-programming relaxation. -/
theorem fractional_iff_classical (p : P) :
    (∃ t,FractionalCompletes p t) ↔ ∃ f,ClassicalCompletes p f := by
  exact ⟨fun ⟨_,ht⟩ => fractional_classical ht,
    fun ⟨_,hf⟩ => ⟨_,quantum_fractional (classical_quantum hf)⟩⟩

#print axioms conjecture_four_by_four
#print axioms fractional_iff_classical
end FractionalTwo
