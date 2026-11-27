module
public import Quantum.FractionalThree

/-! Every nontrivial Sudoku size has a strictly positive rational fractional
grid with one common rational orthostochastic matrix for all its lines,
which admits no global quantum realization in any complex measuring basis. -/
@[expose] public section
noncomputable section
namespace FractionalPositiveFamily
open Equiv QuantumSudoku FractionalPolygons.Sudoku FractionalLayouts
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

structure Fractional (p : Site I → Index I → ℚ) : Prop where
  nonnegative : ∀ x a, 0≤p x a
  cell : ∀ x, ∑ a, p x a=1
  row : ∀ r a, ∑ c, p (r,c) a=1
  column : ∀ c a, ∑ r, p (r,c) a=1
  block : ∀ i j a, ∑ t : Index I, p ((i,t.1),(j,t.2)) a=1

/-- One fixed rational orthogonal matrix supplies every probability vector
on each physical line, up to an independent row permutation for that line. -/
structure CommonOrthostochastic (p : Site I → Index I → ℚ)
    (M : Matrix (Index I) (Index I) ℚ) : Prop where
  orthogonal : ∀ i j, ∑ k, M i k*M j k=if i=j then 1 else 0
  row : ∀ r, ∃ σ : Perm (Index I), ∀ c a, p (r,c) a=M (σ c) a^2
  column : ∀ c, ∃ σ : Perm (Index I), ∀ r a, p (r,c) a=M (σ r) a^2
  block : ∀ i j, ∃ σ : Perm (Index I), ∀ (t : Index I) a,
    p ((i,t.1),(j,t.2)) a=M (σ t) a^2

theorem common (g : Marked I) : CommonOrthostochastic g.p g.B.m := by
  have line (d : Direction) (k : Index I) : ∃ σ : Perm (Index I), ∀ i a,
      g.p (arrange d (k,i)) a=g.B.m (σ i) a^2 := by
    obtain ⟨σ,h⟩ := g.lines d k
    exact ⟨σ,fun j a => congrFun (h j) a⟩
  exact ⟨g.B.gram,line .row,line .column,fun i j => line .block (i,j)⟩

theorem positive (g : Marked I) : ∀ x a, 0<g.p x a := by
  rintro ⟨r,c⟩ a
  obtain ⟨σ,h⟩ := (common g).row r
  rw [h]
  exact sq_pos_of_ne_zero (g.B.nz _ _)

theorem fractional (g : Marked I) : Fractional g.p := by
  have normal (i) : ∑ a, g.B.m i a^2=1 := by simpa [pow_two] using g.B.gram i i
  have cols (a) : ∑ i, g.B.m i a^2=1 := by
    simpa [pow_two] using g.B.gram.transpose a a
  have total (d : Direction) (k a : Index I) : ∑ j, g.p (arrange d (k,j)) a=1 := by
    obtain ⟨σ,h⟩ := g.lines d k
    simp_rw [h]
    exact (Equiv.sum_comp σ (fun i => g.B.m i a^2)).trans (cols a)
  refine ⟨fun x a => (positive g x a).le,?_,total .row,total .column,fun i j => total .block (i,j)⟩
  rintro ⟨r,c⟩
  obtain ⟨σ,h⟩ := (common g).row r
  simp_rw [h]
  exact normal _

theorem impossible [Nonempty I] (g : Marked I) :
    ¬Measured (fun x a => (g.p x a:ℝ)) := by
  intro measured
  let q := fun a => (dist g.B (g.B.special 0) a:ℝ)
  have hs (x) : ∑ a, (g.p x a:ℝ)=1 := by exact_mod_cast (fractional g).cell x
  have hp (x a) : 0≤(g.p x a:ℝ) := by exact_mod_cast (fractional g).nonnegative x a
  have same (k : ℕ) (hk : k≤g.length) : (fun a => (g.p (g.walk k) a:ℝ))=q := by
    rw [g.flags k hk]
  have hleft : q g.B.left=(49/100:ℝ) := by dsimp [q,FractionalLayouts.dist]; rw [g.B.massL]; norm_num
  have hright : q g.B.right=(49/100:ℝ) := by dsimp [q,FractionalLayouts.dist]; rw [g.B.massR]; norm_num
  have nec := FractionalOddCycle.measured_cycle _ hp hs measured g.walk g.length g.odd
    g.closes g.edges q same g.B.left g.B.right g.B.distinct (by norm_num) hleft hright
  have short : (g.length:ℝ)≤7 := by exact_mod_cast g.short
  linarith

def allMarked (N : ℕ) (hN : 2≤N) : Marked (Fin N) := by
  let b : FractionalDenseBasis.Basis (Index (Fin N)) := FractionalDenseBasis.ofCard (by
    by_cases h : N=2
    · subst N; left; decide
    · right
      simp only [Fintype.card_prod,Fintype.card_fin]
      have h3 : 3≤N := by omega
      have bound := Nat.mul_le_mul h3 h3
      omega)
  by_cases h : N=3
  · subst N; exact FractionalThree.witness b
  · exact fromLatin (FractionalIntercalate.ofOrders N (by omega)) b

/-- All sizes and all labelled cells, including strict positivity, exact
rational probabilities, complete ordinary fractional Sudoku marginals,
and one fixed full-support rational orthogonal matrix on every line. -/
theorem all_sizes (N : ℕ) (hN : 2≤N) :
    ∃ p : Site (Fin N) → Index (Fin N) → ℚ,
      (∀ x a, 0<p x a) ∧ Fractional p ∧
      (∃ M : Matrix (Index (Fin N)) (Index (Fin N)) ℚ,
        (∀ i j, M i j≠0) ∧ CommonOrthostochastic p M) ∧
      ¬Measured (fun x a => (p x a:ℝ)) := by
  let : NeZero N := ⟨by omega⟩
  let g := allMarked N hN
  exact ⟨g.p,positive g,fractional g,⟨g.B.m,g.B.nz,common g⟩,impossible g⟩

#print axioms all_sizes
end FractionalPositiveFamily
