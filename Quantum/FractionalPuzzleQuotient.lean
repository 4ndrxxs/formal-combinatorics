module
public import Quantum.FractionalPuzzleSolutions

/-! The subpuzzle embedding preserves the full set of quantum completions
up to the independent phases of their unit-vector representatives. -/
@[expose] public section
noncomputable section
namespace SudokuEmbedding
open Function Equiv QuantumSudoku FractionalLayouts PartialSudoku FractionalPolygons.Sudoku
open scoped ComplexConjugate
variable {k n : ℕ} [NeZero k] (L : SudokuSubsquare.Latin (Fin k) (Fin n))

def cutVector (v : H (Fin n)) : H (Fin k) := WithLp.toLp 2 (fun j => v (coord L j))
def restrictBoard (v : Grid (Fin n)) (r c : Sites k) : H (Fin k) :=
  cutVector L (v (coord L r) (coord L c))

omit [NeZero k] in
theorem cut_stretch (v : H (Fin k)) : cutVector L (stretch L v)=v := by
  ext j
  exact stretch_at L _ _

omit [NeZero k] in
theorem cut_smul (z : ℂ) (v : H (Fin n)) : cutVector L (z • v)=z • cutVector L v := rfl

omit [NeZero k] in
theorem stretch_cut (v : H (Fin n)) (hv : ∀ i,i∉Set.range (coord L) → v i=0) :
    stretch L (cutVector L v)=v := by
  ext i
  by_cases hi : i∈Set.range (coord L)
  · obtain ⟨j,rfl⟩ := hi
    exact stretch_at L _ _
  · exact (stretch_out L _ _ hi).trans (hv i hi).symm

theorem quantum_support {p : Puzzle k} {w : Grid (Fin n)} (hw : QuantumCompletes (puzzle L p) w)
    (a b : Sites k) (u : Sites n) (hu : u∉Set.range (coord L)) : w (coord L a) (coord L b) u=0 := by
  obtain ⟨j,hj⟩ := (symbol_bijective L .row (coord L a)).surjective u
  change symbol L (coord L a,j)=u at hj
  have extj : j∉Set.range (coord L) := by
    rintro ⟨i,rfl⟩
    change symbol L (site L (a,i))=u at hj
    rw [symbol_inside] at hj
    exact hu ⟨_,hj⟩
  have outs : (coord L a,j)∉Set.range (site L) :=
    fun hh => extj ((inside_line .row L.tag _ _).mp hh).2
  obtain ⟨z,he⟩ := hw.2 _ _ _ (puzzle_outside L p (coord L a,j) outs)
  have hz := valid_gram hw.1 .row (coord L a) j (coord L b)
  have ne : j≠coord L b := fun eq => extj ⟨b,eq.symm⟩
  change inner ℂ (w (coord L a) j) (w (coord L a) (coord L b))=_ at hz
  rw [ite_eq_right ne,he,hj,inner_smul_left] at hz
  simpa [unitAxis,EuclideanSpace.inner_single_left] using hz

theorem stretch_restrictBoard {p : Puzzle k} {w : Grid (Fin n)} (hw : QuantumCompletes (puzzle L p) w)
    (a b : Sites k) : stretch L (restrictBoard L w a b)=w (coord L a) (coord L b) :=
  stretch_cut L _ (quantum_support L hw a b)

theorem quantum_restrict {p : Puzzle k} {w : Grid (Fin n)} (hw : QuantumCompletes (puzzle L p) w) :
    QuantumCompletes p (restrictBoard L w) := by
  have gram (d : Direction) (a i j : Sites k) :
      inner ℂ (line d (restrictBoard L w) a i) (line d (restrictBoard L w) a j)=if i=j then 1 else 0 := by
    have eql (b : Sites k) : stretch L (line d (restrictBoard L w) a b)=line d w (coord L a) (coord L b) := by
      unfold line
      rw [arrange_lift]
      exact stretch_restrictBoard L hw _ _
    rw [←stretch_inner L,eql,eql,valid_gram hw.1]
    simp [(coord L).injective.eq_iff]
  refine ⟨⟨fun a => basis_of_gram _ (gram .row a),fun a => basis_of_gram _ (gram .column a),
    fun a b => basis_of_gram _ (gram .block (a,b))⟩,?_⟩
  intro r c i hi
  have hp : puzzle L p (coord L r) (coord L c)=some (coord L i) :=
    (puzzle_inside L p (r,c)).trans (by simp [hi])
  obtain ⟨z,hz⟩ := hw.2 _ _ _ hp
  refine ⟨z,stretch_injective L ?_⟩
  rw [stretch_restrictBoard L hw,stretch_smul,stretch_axis,hz]

theorem board_restrict {p : Puzzle k} {w : Grid (Fin n)} (hw : QuantumCompletes (puzzle L p) w) :
    SameRays w (board L (restrictBoard L w)) := by
  intro r c
  by_cases hi : (r,c)∈Set.range (site L)
  · obtain ⟨s,hs⟩ := hi
    refine ⟨1,?_⟩
    change w (r,c).1 (r,c).2=_ • board L (restrictBoard L w) (r,c).1 (r,c).2
    rw [←hs,board_inside,stretch_restrictBoard L hw]
    simp
    rfl
  · obtain ⟨z,hz⟩ := hw.2 _ _ _ (puzzle_outside L p (r,c) hi)
    exact ⟨z,(board_outside L (restrictBoard L w) (r,c) hi) ▸ hz⟩

omit [NeZero k] in
theorem restrict_board (v : Grid (Fin k)) : restrictBoard L (board L v)=v := by
  funext a b
  have eq : board L v (coord L a) (coord L b)=stretch L (v a b) := board_inside L v (a,b)
  rw [restrictBoard,eq,cut_stretch]

omit [NeZero k] in
theorem restrict_congr {v w : Grid (Fin n)} (h : SameRays v w) : SameRays (restrictBoard L v) (restrictBoard L w) := by
  intro a b
  obtain ⟨z,hz⟩ := h (coord L a) (coord L b)
  exact ⟨z,(congrArg (cutVector L) hz).trans (cut_smul L _ _)⟩

theorem SameRays.refl' {n : ℕ} (v : Grid (Fin n)) : SameRays v v := fun _ _ => ⟨1,by simp⟩

theorem SameRays.symm' {n : ℕ} {u v : Grid (Fin n)} (h : SameRays u v) : SameRays v u := by
  intro a b
  obtain ⟨z,hz⟩ := h a b
  exact ⟨z⁻¹,by rw [hz,smul_smul];simp⟩

theorem SameRays.trans' {n : ℕ} {u v w : Grid (Fin n)} (h : SameRays u v) (h' : SameRays v w) : SameRays u w := by
  intro a b
  obtain ⟨z,hz⟩ := h a b
  obtain ⟨t,ht⟩ := h' a b
  exact ⟨z*t,by rw [hz,ht,smul_smul];rfl⟩

def completionSetoid {n : ℕ} (p : Puzzle n) : Setoid {v : Grid (Fin n) // QuantumCompletes p v} where
  r v w := SameRays v.val w.val
  iseqv := ⟨fun v => SameRays.refl' v.val,fun h => h.symm',fun h h' => h.trans' h'⟩

/-- Quantum solutions as grids of rays, with vector representatives quotiented cell by cell. -/
abbrev QSolutions {n : ℕ} (p : Puzzle n) := Quotient (completionSetoid p)

def quantumEquiv (p : Puzzle k) : QSolutions p ≃ QSolutions (puzzle L p) where
  toFun := Quotient.map (fun v => ⟨board L v.val,quantumCompletes L v.property⟩)
    (fun _ _ h => (sameRays_iff L _ _).mpr h)
  invFun := Quotient.map (fun v => ⟨restrictBoard L v.val,quantum_restrict L v.property⟩) (fun _ _ h => restrict_congr L h)
  left_inv := Quotient.ind (fun v => Quotient.sound (show SameRays (restrictBoard L (board L v.val)) v.val by
    rw [restrict_board];exact SameRays.refl' _))
  right_inv := Quotient.ind (fun v => Quotient.sound (board_restrict L v.property).symm')

#print axioms quantumEquiv
end SudokuEmbedding
