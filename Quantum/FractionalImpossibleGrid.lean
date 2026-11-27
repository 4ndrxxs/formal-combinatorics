module
public import Quantum.FractionalImpossibleTables
public import Quantum.FractionalCyclicLift

/-! The actual normalized quantum completion of the classical partial puzzle. -/
@[expose] public section
noncomputable section
namespace ImpossibleSudoku
open QuantumSudoku FractionalLayouts QuantumCertificate Complex Finset
open scoped BigOperators ComplexConjugate

def numerator (a : Fin 24) (i : Fin 4) : IQ :=
  let v := signed a i
  if lengths[a.val]! = 1 then (2*v,0) else if lengths[a.val]! = 2 then (v,v) else (v,0)

theorem gram_frames : ∀ d k i j, gram 1 (numerator (frame d k i)) (numerator (frame d k j))=
    if i=j then (4,0) else (0,0) := by intro d; cases d <;> decide +kernel

def spread (v : Space 4) : H I := WithLp.toLp 2 (fun p =>
  (Sum.elim (fun j : Fin 4 => v j) (fun _ : U => (0:ℂ))) (symbol.symm p))

theorem spread_inner (v w : Space 4) : inner ℂ (spread v) (spread w)=inner ℂ v w := by
  rw [PiLp.inner_apply,PiLp.inner_apply]
  rw [←symbol.sum_comp (fun p => inner ℂ (spread v p) (spread w p))]
  simp [spread,Fintype.sum_sum_type]

def axisVector (p : Pair) : H I := EuclideanSpace.single p 1

theorem axis_inner (i j : Pair) : inner ℂ (axisVector i) (axisVector j)=if i=j then 1 else 0 := by
  simp [axisVector,EuclideanSpace.inner_single_left,PiLp.single_apply]

theorem outside_inner (v : Space 4) (i : U) :
    inner ℂ (axisVector (symbol (.inr i))) (spread v)=0 := by
  simp [axisVector,EuclideanSpace.inner_single_left,spread]

def vectorOf (n : ℕ) : H I :=
  if h : n<24 then spread (vector 1 4 (numerator ⟨n,h⟩))
  else axisVector (symbol (.inr (Fin.ofNat 1517 (n-24))))

theorem vector_in (h : Fin 24) : vectorOf h.val=spread (vector 1 4 (numerator h)) := by
  simp [vectorOf,h.isLt]

theorem vector_out (u : U) : vectorOf (24+u.val)=axisVector (symbol (.inr u)) := by
  simp [vectorOf,Fin.ofNat, Nat.mod_eq_of_lt u.isLt]

theorem gram_words (d : Direction) (k : I) (s t : Word) :
    inner ℂ (vectorOf (expected d k s)) (vectorOf (expected d k t))=if s=t then 1 else 0 := by
  cases s with
  | inl i =>
    cases t with
    | inl j =>
      change inner ℂ (vectorOf (frame d k i).val) (vectorOf (frame d k j).val)=_
      rw [vector_in,vector_in,spread_inner,inner_vector,gram_frames]
      by_cases h : i=j <;> simp [h]
    | inr j =>
      change inner ℂ (vectorOf (frame d k i).val) (vectorOf (24+j.val))=_
      rw [vector_in,vector_out,←inner_conj_symm,outside_inner]
      simp
  | inr i =>
    cases t with
    | inl j =>
      change inner ℂ (vectorOf (24+i.val)) (vectorOf (frame d k j).val)=_
      rw [vector_out,vector_in,outside_inner]
      simp
    | inr j =>
      change inner ℂ (vectorOf (24+i.val)) (vectorOf (24+j.val))=_
      rw [vector_out,vector_out,axis_inner]
      simp

theorem face_gram (d : Direction) (k : I) (a b : Pair) :
    inner ℂ (vectorOf (face tag d k a)) (vectorOf (face tag d k b))=if a=b then 1 else 0 := by
  obtain ⟨i,rfl⟩ := (ordered d k).surjective a
  obtain ⟨j,rfl⟩ := (ordered d k).surjective b
  rw [ordered_apply,ordered_apply,index_correct,index_correct,gram_words]
  simp [(placement_inj d k).eq_iff]

def board (r c : Pair) : H I := vectorOf (tag r.2 c.2 (r.1+c.1))

theorem board_valid : Valid board := by
  exact SudokuCyclicLift.valid (fun r c t => vectorOf (tag r c t))
    (face_gram .row) (face_gram .column) (face_gram .block)

def clueAt (z : ℕ) : Option Pair :=
  if z<24 then none else some (symbol (.inr (Fin.ofNat 1517 (z-24))))

def puzzle (r c : Pair) : Option Pair := clueAt (tag r.2 c.2 (r.1+c.1))

/-- Prescribed computational basis rays agree up to their projective phase. -/
def QuantumCompletes (p : Pair→Pair→Option Pair) (v : Grid I) : Prop :=
  Valid v ∧ ∀ r c k, p r c=some k → ∃ a : Circle, v r c=(a:ℂ) • axisVector k

theorem quantum_completion : QuantumCompletes puzzle board := by
  refine ⟨board_valid,?_⟩
  intro r c k h
  unfold puzzle clueAt at h
  split at h
  · simp at h
  · rename_i hz
    obtain rfl := Option.some.inj h
    exact ⟨1,by simp [board,vectorOf,hz]⟩

#print axioms quantum_completion
end ImpossibleSudoku
