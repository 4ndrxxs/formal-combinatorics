module
public import Quantum.SudokuQuantumContinuum

/-! For every finite classical partial Sudoku, the projective quantum solution
space is either exactly the set of classical solutions or contains a circle.
This is a statement about the number of solutions of one partial puzzle. -/
@[expose] public section
noncomputable section
namespace SudokuLocus
open Function QuantumSudoku PartialSudoku FractionalLayouts SudokuEmbedding

variable {n : ℕ} [NeZero n]

def classicalBoard (f : Solution n) : Grid (Fin n) := fun r c => unitAxis (f r c)

theorem coord_phase_unique {a b : Sites n} {z t : Circle}
    (h : (z:ℂ) • unitAxis a=(t:ℂ) • unitAxis b) : a=b := by
  by_contra ne
  have eq := congrArg (fun w : H (Fin n) => w a) h
  simpa [unitAxis,PiLp.single_apply,ne,Circle.coe_ne_zero] using eq

theorem classical_quantum {p : Puzzle n} {f : Solution n} (h : ClassicalCompletes p f) :
    QuantumCompletes p (classicalBoard f) := by
  have gram (d : Direction) (k a b : Sites n) :
      inner ℂ (line d (classicalBoard f) k a) (line d (classicalBoard f) k b)=if a=b then 1 else 0 := by
    simp only [line,classicalBoard,axis_inner,(h.1 d k).injective.eq_iff]
  refine ⟨⟨fun r => basis_of_gram _ (gram .row r),fun c => basis_of_gram _ (gram .column c),
    fun i j => basis_of_gram _ (gram .block (i,j))⟩,?_⟩
  intro r c k printed
  exact ⟨1,by simp [classicalBoard,h.2 r c k printed]⟩

def classicalEmbedding (p : Puzzle n) : {f : Solution n // ClassicalCompletes p f} ↪ QSolutions p where
  toFun f := Quotient.mk _ ⟨classicalBoard f.val,classical_quantum f.property⟩
  inj' := by
    intro f g eq
    apply Subtype.ext
    funext r c
    have rays : SameRays (classicalBoard f.val) (classicalBoard g.val) := Quotient.exact eq
    obtain ⟨z,h⟩:=rays r c
    exact coord_phase_unique (z:=1) (t:=z) (by simpa [classicalBoard] using h)

def Mixed (v : Grid (Fin n)) : Prop := ∃ r c a b, a≠b ∧ v r c a≠0 ∧ v r c b≠0

private theorem cell_norm {v : Grid (Fin n)} (h : Valid v) (r c : Sites n) : ‖v r c‖=1 := by
  obtain ⟨B,hB⟩:=h.row r
  exact (congrArg (fun w : Sites n→H (Fin n) => ‖w c‖) hB).symm.trans (B.orthonormal.norm_eq_one c)

private theorem axis_of_sparse (w : H (Fin n)) (hw : ‖w‖=1)
    (no : ∀ a b : Sites n, a≠b → w a≠0 → w b=0) :
    ∃ a : Sites n, ∃ z : Circle,w=(z:ℂ) • unitAxis a := by
  classical
  obtain ⟨a,ha⟩ : ∃ a, w a≠0 := by
    by_contra! all
    have zero : w=0 := by ext j;exact all j
    simp [zero] at hw
  have eq : w=(w a) • unitAxis a := by
    ext j
    by_cases e : j=a
    · simp [e,unitAxis,PiLp.single_apply]
    · simp [e,unitAxis,PiLp.single_apply,no a j (Ne.symm e) ha]
  have unit_a : ‖unitAxis a‖=1 := by simp [unitAxis,EuclideanSpace.single,PiLp.norm_single]
  have z_norm : ‖w a‖=1 := by
    have normeq:=congrArg norm eq
    simpa [norm_smul,unit_a,hw] using normeq.symm
  exact ⟨a,⟨w a,by change w a∈Metric.sphere (0:ℂ) 1;simpa [Metric.mem_sphere] using z_norm⟩,eq⟩

theorem classical_of_axes {p : Puzzle n} {v : Grid (Fin n)} (h : QuantumCompletes p v)
    {f : Solution n} (phases : SameRays v (classicalBoard f)) : ClassicalCompletes p f := by
  constructor
  · intro d k
    apply Finite.injective_iff_bijective.mp
    intro a b eq
    by_contra ne
    let s := arrange d (k,a)
    let t := arrange d (k,b)
    obtain ⟨z,hz⟩:=phases s.1 s.2
    obtain ⟨w,hw⟩:=phases t.1 t.2
    have ortho:=valid_gram h.1 d k a b
    change inner ℂ (v s.1 s.2) (v t.1 t.2)=_ at ortho
    change f s.1 s.2=f t.1 t.2 at eq
    change v s.1 s.2=(z:ℂ) • unitAxis (f s.1 s.2) at hz
    change v t.1 t.2=(w:ℂ) • unitAxis (f t.1 t.2) at hw
    simp [hz,hw,eq,inner_smul_left,inner_smul_right,axis_inner,ne,Circle.coe_ne_zero] at ortho
    simpa [unitAxis] using ortho
  · intro r c j printed
    obtain ⟨z,hz⟩:=phases r c
    obtain ⟨t,ht⟩:=h.2 r c j printed
    exact coord_phase_unique (hz.symm.trans ht)

theorem coordinates_of_not_mixed {p : Puzzle n} {v : Grid (Fin n)} (h : QuantumCompletes p v)
    (no : ¬Mixed v) : ∃ f : Solution n, ClassicalCompletes p f ∧ SameRays v (classicalBoard f) := by
  have axes (r c : Sites n) : ∃ a : Sites n,∃ z : Circle,v r c=(z:ℂ) • unitAxis a :=
    axis_of_sparse _ (cell_norm h.1 r c) (fun a b ne ha => by
      by_contra hb
      exact no ⟨r,c,a,b,ne,ha,hb⟩)
  choose f z hz using axes
  have rays : SameRays v (classicalBoard f) := fun r c => ⟨z r c,hz r c⟩
  exact ⟨f,classical_of_axes h rays,rays⟩

theorem classical_or_circle (p : Puzzle n) :
    Surjective (classicalEmbedding p) ∨ Nonempty (Circle ↪ QSolutions p) := by
  classical
  by_cases mixed : ∃ v : Grid (Fin n), QuantumCompletes p v ∧ Mixed v
  · obtain ⟨v,h,r,c,a,b,hab,ha,hb⟩:=mixed
    exact Or.inr ⟨SudokuContinuum.circleEmbedding h hab ha hb⟩
  · left
    intro q
    obtain ⟨⟨v,h⟩,rfl⟩:=Quotient.exists_rep q
    obtain ⟨f,hf,phase⟩:=coordinates_of_not_mixed h (fun hv => mixed ⟨v,h,hv⟩)
    exact ⟨⟨f,hf⟩,Quotient.sound phase.symm'⟩

#print axioms classical_or_circle
end SudokuLocus
