module
public import Quantum.FractionalPuzzleEmbedding
public import Quantum.FractionalImpossible7

/-! The larger puzzle has exactly the classical completions of its embedded
subpuzzle. Every pair of projectively distinct quantum completions stays distinct. -/
@[expose] public section
noncomputable section
namespace SudokuEmbedding
open Function Equiv Finset QuantumSudoku FractionalLayouts PartialSudoku FractionalPolygons.Sudoku
variable {k n : ℕ} [NeZero k] (L : SudokuSubsquare.Latin (Fin k) (Fin n))

def insertSolution (f : Solution k) (r c : Sites n) : Sites n :=
  fill L.tag (fun q => coord L (f q.1 q.2)) (symbol L) (r,c)

omit [NeZero k] in
theorem insert_inside (f : Solution k) (s : Site (Fin k)) :
    insertSolution L f (site L s).1 (site L s).2=coord L (f s.1 s.2) := fill_at _ _ _ _

omit [NeZero k] in
theorem insert_outside (f : Solution k) (s : Site (Fin n)) (h : s∉Set.range (site L)) :
    insertSolution L f s.1 s.2=symbol L s := by
  rcases s with ⟨r,c⟩
  unfold insertSolution fill
  exact Function.extend_apply' _ (symbol L) (r,c) h

theorem classical_insert {p : Puzzle k} {f : Solution k} (hf : ClassicalCompletes p f) :
    ClassicalCompletes (puzzle L p) (insertSolution L f) := by
  constructor
  · intro d a
    have perm (b : Sites k) : ∃ σ : Perm (Sites k),∀ i,
        coord L (f (arrange d (b,i)).1 (arrange d (b,i)).2)=symbol L (site L (arrange d (b,σ i))) := by
      let F := Equiv.ofBijective _ (hf.1 d b)
      let G := Equiv.ofBijective _ (symbol_bijective (SudokuSubsquare.Latin.cyclic (Fin k)) d b)
      refine ⟨F.trans G.symm,fun i => ?_⟩
      rw [symbol_inside]
      congr 1
      exact (G.apply_symm_apply (F i)).symm
    obtain ⟨ρ,hρ⟩ := shuffled d L.tag (fun q => coord L (f q.1 q.2)) (symbol L) perm a
    have eq : (fun j : Sites n => insertSolution L f (arrange d (a,j)).1 (arrange d (a,j)).2)=
        (fun j => symbol L (arrange d (a,ρ j))) := funext hρ
    rw [eq]
    exact (symbol_bijective L d a).comp ρ.bijective
  · intro r c j h
    by_cases hi : (r,c)∈Set.range (site L)
    · obtain ⟨s,hs⟩ := hi
      change puzzle L p (r,c).1 (r,c).2=some j at h
      rw [←hs,puzzle_inside] at h
      obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp h
      change insertSolution L f (r,c).1 (r,c).2=_
      rw [←hs,insert_inside,hf.2 _ _ _ hb]
    · rw [puzzle_outside L p (r,c) hi] at h
      exact (insert_outside L f (r,c) hi).trans (Option.some.inj h)

theorem solution_mem {p : Puzzle k} {g : Solution n} (hg : ClassicalCompletes (puzzle L p) g)
    (a b : Sites k) : g (coord L a) (coord L b)∈Set.range (coord L) := by
  by_contra hn
  obtain ⟨j,hj⟩ := (symbol_bijective L .row (coord L a)).surjective (g (coord L a) (coord L b))
  change symbol L (coord L a,j)=g (coord L a) (coord L b) at hj
  have extj : j∉Set.range (coord L) := by
    rintro ⟨i,rfl⟩
    change symbol L (site L (a,i))=_ at hj
    rw [symbol_inside] at hj
    exact hn ⟨_,hj⟩
  have outs : (coord L a,j)∉Set.range (site L) :=
    fun hh => extj ((inside_line .row L.tag _ _).mp hh).2
  have eq := hg.2 _ _ _ (puzzle_outside L p (coord L a,j) outs)
  have clash : j=coord L b := (hg.1 .row (coord L a)).injective (eq.trans hj)
  exact extj ⟨b,clash.symm⟩

def restrictSolution {p : Puzzle k} {g : Solution n} (hg : ClassicalCompletes (puzzle L p) g)
    (a b : Sites k) : Sites k := (solution_mem L hg a b).choose

theorem restrict_at {p : Puzzle k} {g : Solution n} (hg : ClassicalCompletes (puzzle L p) g)
    (a b : Sites k) : coord L (restrictSolution L hg a b)=g (coord L a) (coord L b) :=
  (solution_mem L hg a b).choose_spec

theorem classical_restrict {p : Puzzle k} {g : Solution n} (hg : ClassicalCompletes (puzzle L p) g) :
    ClassicalCompletes p (restrictSolution L hg) := by
  constructor
  · intro d a
    apply Finite.injective_iff_bijective.mp
    intro i j eq
    have hh := congrArg (coord L) eq
    change coord L (restrictSolution L hg (arrange d (a,i)).1 (arrange d (a,i)).2)=
      coord L (restrictSolution L hg (arrange d (a,j)).1 (arrange d (a,j)).2) at hh
    rw [restrict_at,restrict_at] at hh
    have hh' : g (arrange d (coord L a,coord L i)).1 (arrange d (coord L a,coord L i)).2=
        g (arrange d (coord L a,coord L j)).1 (arrange d (coord L a,coord L j)).2 := by
      rw [arrange_lift,arrange_lift]
      exact hh
    exact (coord L).injective ((hg.1 d _).injective hh')
  · intro r c j h
    apply (coord L).injective
    rw [restrict_at]
    apply hg.2
    exact (puzzle_inside L p (r,c)).trans (by simp [h])

theorem insert_restrict {p : Puzzle k} {g : Solution n} (hg : ClassicalCompletes (puzzle L p) g) :
    insertSolution L (restrictSolution L hg)=g := by
  funext r c
  by_cases hi : (r,c)∈Set.range (site L)
  · obtain ⟨s,hs⟩ := hi
    change insertSolution L (restrictSolution L hg) (r,c).1 (r,c).2=g (r,c).1 (r,c).2
    rw [←hs,insert_inside,restrict_at]
    rfl
  · exact (insert_outside L _ (r,c) hi).trans (hg.2 _ _ _ (puzzle_outside L p (r,c) hi)).symm

/-- Extension and restriction give inverse bijections on actual ordinary solutions. -/
def classicalEquiv (p : Puzzle k) :
    {f : Solution k // ClassicalCompletes p f} ≃ {g : Solution n // ClassicalCompletes (puzzle L p) g} where
  toFun f := ⟨insertSolution L f.val,classical_insert L f.property⟩
  invFun g := ⟨restrictSolution L g.property,classical_restrict L g.property⟩
  left_inv f := by
    apply Subtype.ext
    funext a b
    apply (coord L).injective
    rw [restrict_at]
    exact insert_inside L f.val (a,b)
  right_inv g := Subtype.ext (insert_restrict L g.property)

def SameRays {n : ℕ} (v w : Grid (Fin n)) : Prop := ∀ r c,∃ z : Circle,v r c=(z:ℂ) • w r c

omit [NeZero k] in
theorem stretch_injective : Injective (stretch L) := by
  intro v w h
  ext i
  simpa [stretch_at] using congrArg (fun s : H (Fin n) => s (coord L i)) h

omit [NeZero k] in
theorem sameRays_iff (v w : Grid (Fin k)) : SameRays (board L v) (board L w) ↔ SameRays v w := by
  constructor
  · intro hb r c
    obtain ⟨z,hz⟩ := hb (coord L r) (coord L c)
    have iv : board L v (coord L r) (coord L c)=stretch L (v r c) := board_inside L v (r,c)
    have iw : board L w (coord L r) (coord L c)=stretch L (w r c) := board_inside L w (r,c)
    rw [iv,iw,←stretch_smul] at hz
    exact ⟨z,stretch_injective L hz⟩
  · intro h r c
    by_cases hi : (r,c)∈Set.range (site L)
    · obtain ⟨s,hs⟩ := hi
      obtain ⟨z,he⟩ := h s.1 s.2
      refine ⟨z,?_⟩
      change board L v (r,c).1 (r,c).2=(z:ℂ) • board L w (r,c).1 (r,c).2
      rw [←hs,board_inside,board_inside,he,stretch_smul]
    · exact ⟨1,by rw [board_outside L v (r,c) hi,board_outside L w (r,c) hi];simp⟩

/-- A counterexample for blocks of side seven embeds at every side at least fourteen. -/
theorem counterexamples_large (n : ℕ) (hn : 14≤n) :
    ∃ (p : Puzzle n) (v : Grid (Fin n)),QuantumCompletes p v ∧ ¬∃ g,ClassicalCompletes p g := by
  let L := SudokuSubsquare.ofOrders 7 n (by omega)
  obtain ⟨p,v,hq,hc⟩ := ImpossibleSudoku7.counterexample
  exact ⟨puzzle L p,board L v,quantumCompletes L hq,fun ⟨g,hg⟩ =>
    hc ⟨restrictSolution L hg,classical_restrict L hg⟩⟩

#print axioms classicalEquiv
#print axioms sameRays_iff
#print axioms counterexamples_large
end SudokuEmbedding
