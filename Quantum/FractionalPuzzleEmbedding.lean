module
public import Quantum.FractionalSubsquare
public import Quantum.FractionalPartialBasis

/-! An arbitrary finite SudoQ and each of its prescribed computational rays
embed in a larger Sudoku with a cyclic Latin subsquare. All new cells are fixed. -/
@[expose] public section
noncomputable section
namespace SudokuEmbedding
open Function Equiv Finset QuantumSudoku FractionalLayouts PartialSudoku
  FractionalPolygons.Sudoku
open scoped ComplexConjugate BigOperators

variable {k n : ℕ} [NeZero k]
abbrev Puzzle (k : ℕ) := Sites k → Sites k → Option (Sites k)
abbrev Solution (k : ℕ) := Sites k → Sites k → Sites k

def symbol {K I : Type*} [Add K] (L : SudokuSubsquare.Latin K I) (s : Site I) : Index I :=
  (L.op s.1.2 s.2.1,L.op s.2.2 s.1.1)

theorem symbol_bijective {K I : Type*} [Add K] (L : SudokuSubsquare.Latin K I) (d : Direction)
    (a : Index I) : Bijective (fun b => symbol L (arrange d (a,b))) := by
  let : Nonempty I := ⟨a.1⟩
  rcases a with ⟨i,j⟩
  cases d
  · exact Prod.map_bijective.mpr ⟨L.row j,L.col i⟩
  · exact (Prod.map_bijective.mpr ⟨L.col i,L.row j⟩).comp (Equiv.prodComm _ _).bijective
  · exact Prod.map_bijective.mpr ⟨L.col j,L.col i⟩

variable (L : SudokuSubsquare.Latin (Fin k) (Fin n))

abbrev coord := liftPair L.tag
abbrev site := liftSite L.tag
def bg (s : Site (Fin k)) := symbol (SudokuSubsquare.Latin.cyclic (Fin k)) s

theorem symbol_inside (s : Site (Fin k)) : symbol L (site L s)=coord L (bg s) := by
  rcases s with ⟨⟨a,b⟩,⟨c,d⟩⟩
  change (L.op (L.tag b) (L.tag c),L.op (L.tag d) (L.tag a))=_
  rw [L.sub,L.sub]
  rfl

theorem exterior_symbol (d : Direction) (a : Sites k) (j : Sites n) (h : j∉Set.range (coord L)) :
    symbol L (arrange d (coord L a,j))∉Set.range (coord L) := by
  rintro ⟨b,hb⟩
  obtain ⟨u,hu⟩ := (symbol_bijective (SudokuSubsquare.Latin.cyclic (Fin k)) d a).surjective b
  change bg (arrange d (a,u))=b at hu
  have eq : symbol L (arrange d (coord L a,coord L u))=coord L b := by
    rw [arrange_lift,symbol_inside,hu]
  exact h ⟨u,(symbol_bijective L d _).injective (eq.trans hb)⟩

def stretch (v : H (Fin k)) : H (Fin n) := ∑ j, v j • unitAxis (coord L j)

omit [NeZero k] in
theorem stretch_at (v : H (Fin k)) (j : Sites k) : stretch L v (coord L j)=v j := by
  simp [stretch,unitAxis,Pi.single_apply,(coord L).injective.eq_iff]

omit [NeZero k] in
theorem stretch_out (v : H (Fin k)) (i : Sites n) (h : i∉Set.range (coord L)) :
    stretch L v i=0 := by
  have hn (j : Sites k) : coord L j≠i := fun he => h ⟨j,he⟩
  simp [stretch,unitAxis,hn]

omit [NeZero k] in
theorem stretch_inner (v w : H (Fin k)) : inner ℂ (stretch L v) (stretch L w)=inner ℂ v w := by
  rw [show stretch L v=∑ i,v i • unitAxis (coord L i) by rfl,sum_inner]
  simp [inner_smul_left,unitAxis,stretch_at,PiLp.inner_apply,mul_comm]

omit [NeZero k] in
theorem stretch_smul (z : ℂ) (v : H (Fin k)) : stretch L (z • v)=z • stretch L v := by
  simp [stretch,Finset.smul_sum,smul_smul]

omit [NeZero k] in
theorem stretch_axis (j : Sites k) : stretch L (unitAxis j)=unitAxis (coord L j) := by
  simp [stretch,unitAxis]

omit [NeZero k] in
theorem axis_stretch_out (v : H (Fin k)) (i : Sites n) (h : i∉Set.range (coord L)) :
    inner ℂ (unitAxis i) (stretch L v)=0 := by
  simp [unitAxis,EuclideanSpace.inner_single_left,stretch_out _ _ _ h]

theorem axis_inner (i j : Sites n) : inner ℂ (unitAxis i) (unitAxis j)=if i=j then 1 else 0 := by
  simp [unitAxis,EuclideanSpace.inner_single_left,PiLp.single_apply]

def board (v : Grid (Fin k)) (r c : Sites n) : H (Fin n) :=
  fill L.tag (fun q => stretch L (v q.1 q.2)) (fun q => unitAxis (symbol L q)) (r,c)

omit [NeZero k] in
theorem board_inside (v : Grid (Fin k)) (s : Site (Fin k)) :
    board L v (site L s).1 (site L s).2=stretch L (v s.1 s.2) := fill_at _ _ _ _

omit [NeZero k] in
theorem board_outside (v : Grid (Fin k)) (s : Site (Fin n)) (h : s∉Set.range (site L)) :
    board L v s.1 s.2=unitAxis (symbol L s) := by
  rcases s with ⟨r,c⟩
  unfold board fill
  exact Function.extend_apply' _ (fun q => unitAxis (symbol L q)) (r,c) h

def line {n : ℕ} (d : Direction) (v : Grid (Fin n)) (a b : Sites n) :=
  v (arrange d (a,b)).1 (arrange d (a,b)).2

omit [NeZero k] in
theorem valid_gram {v : Grid (Fin k)} (h : Valid v) (d : Direction) (a i j : Sites k) :
    inner ℂ (line d v a i) (line d v a j)=if i=j then 1 else 0 := by
  have H : BasisLine (line d v a) := by
    cases d with
    | row => exact h.row _
    | column => exact h.column _
    | block => exact h.block a.1 a.2
  obtain ⟨B,hB⟩ := H
  rw [←congrFun hB i,←congrFun hB j,B.inner_eq_ite]

theorem board_gram {v : Grid (Fin k)} (hv : Valid v) (d : Direction) (a i j : Sites n) :
    inner ℂ (line d (board L v) a i) (line d (board L v) a j)=if i=j then 1 else 0 := by
  classical
  have outside (a i : Sites n) (h : ¬(a∈Set.range (coord L) ∧ i∈Set.range (coord L))) :
      line d (board L v) a i=unitAxis (symbol L (arrange d (a,i))) :=
    board_outside _ _ _ (fun hh => h ((inside_line d _ _ _).mp hh))
  have inside (a i : Sites k) : line d (board L v) (coord L a) (coord L i)=stretch L (line d v a i) := by
    unfold line
    rw [arrange_lift,board_inside]
  by_cases ha : a∈Set.range (coord L)
  · obtain ⟨a,rfl⟩ := ha
    by_cases hi : i∈Set.range (coord L) <;> by_cases hj : j∈Set.range (coord L)
    · obtain ⟨r,rfl⟩ := hi
      obtain ⟨c,rfl⟩ := hj
      rw [inside,inside,stretch_inner,valid_gram hv]
      simp [(coord L).injective.eq_iff]
    · obtain ⟨r,rfl⟩ := hi
      rw [inside,outside _ _ (fun hh => hj hh.2),←inner_conj_symm,
        axis_stretch_out L _ _ (exterior_symbol L d a j hj)]
      simp [show coord L r≠j from fun e => hj ⟨r,e⟩]
    · obtain ⟨c,rfl⟩ := hj
      rw [outside _ _ (fun hh => hi hh.2),inside,axis_stretch_out L _ _ (exterior_symbol L d a i hi)]
      simp [show i≠coord L c from fun e => hi ⟨c,e.symm⟩]
    · rw [outside _ _ (fun hh => hi hh.2),outside _ _ (fun hh => hj hh.2),axis_inner]
      simp [(symbol_bijective L d _).injective.eq_iff]
  · rw [outside _ _ (fun hh => ha hh.1),outside _ _ (fun hh => ha hh.1),axis_inner]
    simp [(symbol_bijective L d _).injective.eq_iff]

theorem board_valid (v : Grid (Fin k)) (hv : Valid v) : Valid (board L v) := by
  let : Nonempty (Fin n) := ⟨L.tag 0⟩
  constructor
  · intro a; exact basis_of_gram _ (board_gram L hv .row a)
  · intro a; exact basis_of_gram _ (board_gram L hv .column a)
  · intro a b; exact basis_of_gram _ (board_gram L hv .block (a,b))

def puzzle (p : Puzzle k) (r c : Sites n) : Option (Sites n) :=
  fill L.tag (fun q => (p q.1 q.2).map (coord L)) (fun q => some (symbol L q)) (r,c)

omit [NeZero k] in
theorem puzzle_inside (p : Puzzle k) (s : Site (Fin k)) :
    puzzle L p (site L s).1 (site L s).2=(p s.1 s.2).map (coord L) := fill_at _ _ _ _

omit [NeZero k] in
theorem puzzle_outside (p : Puzzle k) (s : Site (Fin n)) (h : s∉Set.range (site L)) :
    puzzle L p s.1 s.2=some (symbol L s) := by
  rcases s with ⟨r,c⟩
  unfold puzzle fill
  exact Function.extend_apply' _ (fun q => some (symbol L q)) (r,c) h

theorem quantumCompletes {p : Puzzle k} {v : Grid (Fin k)} (hv : QuantumCompletes p v) :
    QuantumCompletes (puzzle L p) (board L v) := by
  refine ⟨board_valid L v hv.1,?_⟩
  intro r c t h
  by_cases hi : (r,c)∈Set.range (site L)
  · obtain ⟨s,hs⟩ := hi
    change puzzle L p (r,c).1 (r,c).2=some t at h
    rw [←hs,puzzle_inside] at h
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨z,he⟩ := hv.2 _ _ _ ha
    refine ⟨z,?_⟩
    change board L v (r,c).1 (r,c).2=_
    rw [←hs,board_inside,he,stretch_smul,stretch_axis]
  · rw [puzzle_outside L p (r,c) hi] at h
    obtain rfl := Option.some.inj h
    refine ⟨1,?_⟩
    rw [board_outside L v (r,c) hi]
    simp

#print axioms quantumCompletes
end SudokuEmbedding
