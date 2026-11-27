module
public import Quantum.FractionalImpossibleGrid

/-! A finite four-ray-per-slice certificate gives a physical quantum
completion with all remaining symbols printed as coordinate vectors. -/
@[expose] public section
noncomputable section
namespace PartialSudoku
open QuantumSudoku FractionalLayouts QuantumCertificate Finset Complex
open scoped BigOperators ComplexConjugate

abbrev Sites (n : ℕ) := Index (Fin n)
abbrev Word (m : ℕ) := Fin 4 ⊕ Fin m
abbrev Code (m : ℕ) := Fin 24 ⊕ Fin m
def unitAxis {n : ℕ} (i : Sites n) : H (Fin n) := EuclideanSpace.single i 1

def QuantumCompletes {n : ℕ} (p : Sites n→Sites n→Option (Sites n)) (v : Grid (Fin n)) : Prop :=
  Valid v ∧ ∀ r c k, p r c=some k → ∃ z : Circle,v r c=(z:ℂ) • unitAxis k

def ClassicalCompletes {n : ℕ} (p : Sites n→Sites n→Option (Sites n)) (f : Sites n→Sites n→Sites n) : Prop :=
  (∀ d k, Function.Bijective (fun j : Sites n => f (arrange d (k,j)).1 (arrange d (k,j)).2)) ∧
  ∀ r c k, p r c=some k → f r c=k

def slice {n : ℕ} {α : Type*} (T : Fin n→Fin n→Fin n→α) (d : Direction) (k : Fin n) (p : Sites n) : α :=
  match d with | .row => T k p.1 p.2 | .column => T p.1 k p.2 | .block => T p.1 p.2 k

structure Layout (n m : ℕ) where
  dims : 4+m=n*n
  label : Fin n→Fin n→Fin n→Code m
  place : Direction→Fin n→Word m→Sites n
  frame : Direction→Fin n→Fin 4→Fin 24
  checked : ∀ d k s,slice label d k (place d k s)=
    Sum.elim (fun h => Sum.inl (frame d k h)) Sum.inr s
  ortho : ∀ d k i j, gram 1 (ImpossibleSudoku.numerator (frame d k i))
    (ImpossibleSudoku.numerator (frame d k j))=if i=j then (4,0) else (0,0)

variable {n m : ℕ} [NeZero n] (L : Layout n m)

def Layout.symbol : Word m ≃ Sites n := Fintype.equivOfCardEq (by simpa [Word,Sites,Index] using L.dims)

def Layout.spread (v : Space 4) : H (Fin n) := WithLp.toLp 2 (fun p =>
  Sum.elim (fun j : Fin 4 => v j) (fun _ : Fin m => (0:ℂ)) (L.symbol.symm p))

theorem Layout.spread_inner (v w : Space 4) : inner ℂ (L.spread v) (L.spread w)=inner ℂ v w := by
  rw [PiLp.inner_apply,PiLp.inner_apply]
  rw [←L.symbol.sum_comp (fun p => inner ℂ (L.spread v p) (L.spread w p))]
  simp [Layout.spread,Fintype.sum_sum_type]

def Layout.vector : Code m→H (Fin n)
  | .inl k => L.spread (QuantumCertificate.vector 1 4 (ImpossibleSudoku.numerator k))
  | .inr u => unitAxis (L.symbol (.inr u))

def Layout.line (d : Direction) (k : Fin n) : Word m→H (Fin n) :=
  Sum.elim (fun h => L.vector (.inl (L.frame d k h))) (fun u => L.vector (.inr u))

theorem Layout.line_gram (d : Direction) (k : Fin n) (s t : Word m) :
    inner ℂ (L.line d k s) (L.line d k t)=if s=t then 1 else 0 := by
  have b (i : Fin m) (v : Space 4) : inner ℂ (unitAxis (L.symbol (.inr i))) (L.spread v)=0 := by
    simp [unitAxis,EuclideanSpace.inner_single_left,Layout.spread]
  cases s with
  | inl i =>
    cases t with
    | inl j =>
      simp only [Layout.line,Layout.vector,Sum.elim_inl,L.spread_inner,inner_vector,L.ortho]
      by_cases h : i=j <;> simp [h]
    | inr j =>
      simp only [Layout.line,Layout.vector,Sum.elim_inl,Sum.elim_inr]
      rw [←inner_conj_symm,b]
      simp
  | inr i =>
    cases t with
    | inl j => simp [Layout.line,Layout.vector,b]
    | inr j => simp [Layout.line,Layout.vector,unitAxis,EuclideanSpace.inner_single_left,PiLp.single_apply]

theorem Layout.line_at (d : Direction) (k : Fin n) (s : Word m) :
    L.vector (slice L.label d k (L.place d k s))=L.line d k s := by
  rw [L.checked]
  cases s <;> rfl

theorem Layout.place_inj (d : Direction) (k : Fin n) : Function.Injective (L.place d k) := by
  intro s t he
  by_contra hn
  have eq : L.line d k s=L.line d k t := by rw [←L.line_at,←L.line_at,he]
  have zero := L.line_gram d k s t
  rw [if_neg hn,eq,L.line_gram,if_pos rfl] at zero
  exact one_ne_zero zero

def Layout.ordered (d : Direction) (k : Fin n) : Word m ≃ Sites n :=
  L.symbol.trans (Equiv.ofBijective (fun p => L.place d k (L.symbol.symm p))
    (Finite.injective_iff_bijective.mp ((L.place_inj d k).comp L.symbol.symm.injective)))

@[simp] theorem Layout.ordered_apply (d : Direction) (k : Fin n) (s : Word m) :
    L.ordered d k s=L.place d k s := by simp [Layout.ordered]

theorem Layout.slice_gram (d : Direction) (k : Fin n) (a b : Sites n) :
    inner ℂ (L.vector (slice L.label d k a)) (L.vector (slice L.label d k b))=if a=b then 1 else 0 := by
  obtain ⟨i,rfl⟩ := (L.ordered d k).surjective a
  obtain ⟨j,rfl⟩ := (L.ordered d k).surjective b
  rw [Layout.ordered_apply,Layout.ordered_apply,L.line_at,L.line_at,L.line_gram]
  simp [(L.place_inj d k).eq_iff]

def Layout.board : Grid (Fin n) := SudokuCyclicLift.board (fun r c t => L.vector (L.label r c t))
def Layout.given (a : Code m) : Option (Sites n) :=
  match a with | .inl _ => none | .inr u => some (L.symbol (.inr u))
def Layout.puzzle (r c : Sites n) := L.given (L.label r.2 c.2 (r.1+c.1))

theorem Layout.quantum : QuantumCompletes L.puzzle L.board := by
  constructor
  · exact SudokuCyclicLift.valid (fun r c t => L.vector (L.label r c t))
      (L.slice_gram .row) (L.slice_gram .column) (L.slice_gram .block)
  · intro r c k h
    change L.given (L.label r.2 c.2 (r.1+c.1))=some k at h
    change ∃ z : Circle,L.vector (L.label r.2 c.2 (r.1+c.1))=(z:ℂ) • unitAxis k
    cases he : L.label r.2 c.2 (r.1+c.1) with
    | inl i => simp [he,Layout.given] at h
    | inr e =>
      have eq : L.symbol (.inr e)=k := by simpa [he,Layout.given] using h
      exact ⟨1,by simp [Layout.vector,eq]⟩

#print axioms Layout.quantum
end PartialSudoku
