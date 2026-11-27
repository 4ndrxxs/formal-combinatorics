module
public import Quantum.FractionalPartialCut

/-! A direct certificate for all physical row, column and block contexts of a
rank-four partial Sudoku, with arbitrary parity selections on the physical lines. -/
@[expose] public section
noncomputable section
namespace PhysicalSudokuCut
open QuantumSudoku FractionalLayouts PartialSudoku QuantumCertificate Finset Complex
open scoped BigOperators ComplexConjugate

def physicalSlice {n : ℕ} {α : Type*} (T : Sites n → Sites n → α) (d : Direction)
    (k j : Sites n) : α := T (arrange d (k,j)).1 (arrange d (k,j)).2

structure Full (n m : ℕ) where
  dims : 4+m=n*n
  label : Sites n → Sites n → Code m
  place : Direction → Sites n → Word m → Sites n
  frame : Direction → Sites n → Fin 4 → Fin 24
  checked : ∀ d k s, physicalSlice label d k (place d k s)=
    Sum.elim (fun h => Sum.inl (frame d k h)) Sum.inr s
  ortho : ∀ d k i j, gram 1 (ImpossibleSudoku.numerator (frame d k i))
    (ImpossibleSudoku.numerator (frame d k j))=if i=j then (4,0) else (0,0)

variable {n m : ℕ} [NeZero n] (L : Full n m)

def Full.symbol : Word m ≃ Sites n := Fintype.equivOfCardEq (by simpa [Word,Sites,Index] using L.dims)

def Full.spread (v : Space 4) : H (Fin n) := WithLp.toLp 2 (fun p =>
  Sum.elim (fun j : Fin 4 => v j) (fun _ : Fin m => (0:ℂ)) (L.symbol.symm p))

theorem Full.spread_inner (v w : Space 4) : inner ℂ (L.spread v) (L.spread w)=inner ℂ v w := by
  rw [PiLp.inner_apply,PiLp.inner_apply]
  rw [←L.symbol.sum_comp (fun p => inner ℂ (L.spread v p) (L.spread w p))]
  simp [Full.spread,Fintype.sum_sum_type]

def Full.vector : Code m→H (Fin n)
  | .inl k => L.spread (QuantumCertificate.vector 1 4 (ImpossibleSudoku.numerator k))
  | .inr u => unitAxis (L.symbol (.inr u))

def Full.line (d : Direction) (k : Sites n) : Word m→H (Fin n) :=
  Sum.elim (fun h => L.vector (.inl (L.frame d k h))) (fun u => L.vector (.inr u))

theorem Full.line_gram (d : Direction) (k : Sites n) (s t : Word m) :
    inner ℂ (L.line d k s) (L.line d k t)=if s=t then 1 else 0 := by
  have b (i : Fin m) (v : Space 4) : inner ℂ (unitAxis (L.symbol (.inr i))) (L.spread v)=0 := by
    simp [unitAxis,EuclideanSpace.inner_single_left,Full.spread]
  cases s with
  | inl i =>
    cases t with
    | inl j =>
      simp only [Full.line,Full.vector,Sum.elim_inl,L.spread_inner,inner_vector,L.ortho]
      by_cases h : i=j <;> simp [h]
    | inr j =>
      simp only [Full.line,Full.vector,Sum.elim_inl,Sum.elim_inr]
      rw [←inner_conj_symm,b]
      simp
  | inr i =>
    cases t with
    | inl j => simp [Full.line,Full.vector,b]
    | inr j => simp [Full.line,Full.vector,unitAxis,EuclideanSpace.inner_single_left,PiLp.single_apply]

theorem Full.line_at (d : Direction) (k : Sites n) (s : Word m) :
    L.vector (physicalSlice L.label d k (L.place d k s))=L.line d k s := by
  rw [L.checked]
  cases s <;> rfl

theorem Full.place_inj (d : Direction) (k : Sites n) : Function.Injective (L.place d k) := by
  intro s t he
  by_contra hn
  have eq : L.line d k s=L.line d k t := by rw [←L.line_at,←L.line_at,he]
  have zero := L.line_gram d k s t
  rw [if_neg hn,eq,L.line_gram,if_pos rfl] at zero
  exact one_ne_zero zero

def Full.ordered (d : Direction) (k : Sites n) : Word m ≃ Sites n :=
  L.symbol.trans (Equiv.ofBijective (fun p => L.place d k (L.symbol.symm p))
    (Finite.injective_iff_bijective.mp ((L.place_inj d k).comp L.symbol.symm.injective)))

@[simp] theorem Full.ordered_apply (d : Direction) (k : Sites n) (s : Word m) :
    L.ordered d k s=L.place d k s := by simp [Full.ordered]

theorem Full.slice_gram (d : Direction) (k : Sites n) (a b : Sites n) :
    inner ℂ (L.vector (physicalSlice L.label d k a)) (L.vector (physicalSlice L.label d k b))=if a=b then 1 else 0 := by
  obtain ⟨i,rfl⟩ := (L.ordered d k).surjective a
  obtain ⟨j,rfl⟩ := (L.ordered d k).surjective b
  rw [Full.ordered_apply,Full.ordered_apply,L.line_at,L.line_at,L.line_gram]
  simp [(L.place_inj d k).eq_iff]

def Full.board : Grid (Fin n) := fun r c => L.vector (L.label r c)
def Full.given : Code m → Option (Sites n)
  | .inl _ => none
  | .inr u => some (L.symbol (.inr u))
def Full.puzzle (r c : Sites n) := L.given (L.label r c)

theorem Full.quantum : QuantumCompletes L.puzzle L.board := by
  constructor
  · refine ⟨fun k => basis_of_gram _ (L.slice_gram .row k),
      fun k => basis_of_gram _ (L.slice_gram .column k),
      fun i j => basis_of_gram _ (L.slice_gram .block (i,j))⟩
  · intro r c k h
    change L.given (L.label r c)=some k at h
    change ∃ z : Circle,L.vector (L.label r c)=(z:ℂ) • unitAxis k
    cases eq : L.label r c with
    | inl i => simp [eq,Full.given] at h
    | inr u => exact ⟨1,by simpa [Full.given,eq,Full.vector] using
                         congrArg unitAxis (Option.some.inj (by simpa [Full.given,eq] using h))⟩

structure Cut (L : Full n m) where
  mark : Direction → Sites n → ZMod 2
  active : ∀ r c, (L.label r c).isLeft=true →
    mark .row r + mark .column c + mark .block (r.1,c.1)=0
  odd : (∑ k,mark .row k)+(∑ k,mark .column k)+(∑ k,mark .block k)≠0

theorem Cut.impossible (K : Cut L) : ¬∃ f,ClassicalCompletes L.puzzle f := by
  classical
  rintro ⟨f,hf⟩
  let bit (p : Sites n × Sites n) : ZMod 2 := if f p.1 p.2=L.symbol (.inl 0) then 1 else 0
  let weight (d : Direction) (p : Sites n × Sites n) : ZMod 2 :=
    K.mark d ((arrange d).symm p).1
  have one (d : Direction) (k : Sites n) : (∑ j,bit (arrange d (k,j)))=1 := by
    let e := Equiv.ofBijective (fun j : Sites n => f (arrange d (k,j)).1 (arrange d (k,j)).2) (hf.1 d k)
    simpa [e,bit] using Equiv.sum_comp e (fun a : Sites n => if a=L.symbol (.inl 0) then (1:ZMod 2) else 0)
  have total (d) : (∑ p,weight d p*bit p)=∑ k,K.mark d k := by
    rw [← Equiv.sum_comp (arrange d) (fun p => weight d p * bit p),Fintype.sum_prod_type]
    apply sum_congr rfl
    intro k _
    simp [weight,← Finset.mul_sum,one]
  have zero (p : Sites n × Sites n) :
      (weight .row p+weight .column p+weight .block p)*bit p = 0 := by
    obtain ⟨r,c⟩ := p
    cases e : L.label r c with
    | inl v =>
      have h := K.active r c (by simp [e])
      change (K.mark .row r+K.mark .column c+K.mark .block (r.1,c.1))*_=0
      rw [h,zero_mul]
    | inr u =>
      have clue : L.puzzle r c=some (L.symbol (.inr u)) := by simp [Full.puzzle,e,Full.given]
      simp [bit,hf.2 r c _ clue]
  have z : (∑ p,(weight .row p+weight .column p+weight .block p)*bit p)=0 := by simp [zero]
  simp only [add_mul,Finset.sum_add_distrib,total] at z
  exact K.odd z

theorem counterexample (K : Cut L) :
    ∃ (p : Sites n→Sites n→Option (Sites n)) (v : Grid (Fin n)),
      QuantumCompletes p v ∧ ¬∃ f, ClassicalCompletes p f :=
  ⟨L.puzzle,L.board,L.quantum,K.impossible L⟩

#print axioms counterexample
end PhysicalSudokuCut
