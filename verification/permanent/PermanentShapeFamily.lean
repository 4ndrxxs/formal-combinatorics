import PermanentLineFamily
import PermanentShapeBoards

/-! Equivariance and one-cell deletion for the complete list of possible
pivot shapes. Each rank certificate is tested at a centre supported on the
particular board under consideration. -/
noncomputable section
open Matrix Module Equiv Finset QuinticPencil
namespace PermanentFive
variable {K : Type*} [Field K]

/-- Orbit under row permutations, column permutations and transposition. -/
inductive SameBoard (model : Finset Cell) : Finset Cell → Prop
  | refl : SameBoard model model
  | move {S : Finset Cell} (e : Perm Cell) (act : GridAction e)
      (prior : SameBoard model (S.map e.symm.toEmbedding)) : SameBoard model S

theorem SameBoard.card_eq {M S : Finset Cell} (h : SameBoard M S) : S.card = M.card := by
  induction h with
  | refl => rfl
  | move _ _ _ ih => simpa using ih

def ShapeAllowed (S : Finset Cell) : Prop := ∃ i, SameBoard (shapeModel i) S

def AmbientWitness (K : Type*) [Field K] (S : Finset Cell) (r : ℕ) : Prop :=
  ∃ z : Cell → K, (∀ i ∉ S, z i = 0) ∧ r ≤ (hessian (per K Idx) z).rank

theorem ambient_of_integer_minor (K : Type*) [Field K] [CharZero K] {d : ℕ}
    (S : Finset Cell) (r c : Fin d → Cell) (A : Matrix (Fin d) (Fin d) ℤ)
    (entries : ∀ i j, secondAt (boardPoint S) (r i) (c j) = A i j) (unit : A.det ≠ 0) :
    AmbientWitness K S d := by
  refine ⟨(Int.castRingHom K) ∘ boardPoint S,?_,?_⟩
  · intro i hi; simp [boardPoint,hi]
  · simpa only [Fintype.card_fin] using integer_hessian_rank K _ r c A entries unit

def ShapeTest (K : Type*) [Field K] (S : Finset Cell) : Prop :=
  ContainsFullLine S → ShapeAllowed S ∨ ∃ r, AmbientWitness K S r ∧ S.card < r+5

def ShapeFamily (K : Type*) [Field K] (T : Finset Cell) : Prop := ∀ S ⊆ T, ShapeTest K S

private theorem full_moves {S : Finset Cell} (e : Perm Cell) (act : GridAction e)
    (h : ContainsFullLine S) : ContainsFullLine (S.map e.toEmbedding) := by
  obtain ⟨axis,i,h⟩ := h
  have mem (j : Idx) : e (linePoint axis i j) ∈ S.map e.toEmbedding :=
    Finset.mem_map.mpr ⟨_,h j,rfl⟩
  cases act with
  | rowCol r c =>
    cases axis with
    | false => exact ⟨false,r i,fun j ↦ by simpa [linePoint] using mem (c.symm j)⟩
    | true => exact ⟨true,c i,fun j ↦ by simpa [linePoint] using mem (r.symm j)⟩
  | transpose =>
    cases axis with
    | false => exact ⟨true,i,mem⟩
    | true => exact ⟨false,i,mem⟩

private theorem action_symm {e : Perm Cell} (act : GridAction e) : GridAction e.symm := by
  cases act with
  | rowCol r c => exact .rowCol r.symm c.symm
  | transpose => exact .transpose

theorem AmbientWitness.relabel {A B : Finset Cell} {r : ℕ} (h : AmbientWitness K A r)
    (e : Perm Cell) (sym : MvPolynomial.rename e (per K Idx) = per K Idx)
    (inside : ∀ i ∈ A, e i ∈ B) : AmbientWitness K B r := by
  obtain ⟨z,support,rk⟩ := h
  refine ⟨z ∘ e.symm,?_,?_⟩
  · intro i hi
    apply support
    intro ha
    exact hi (by simpa using inside _ ha)
  · rwa [(transport e sym z).2]

theorem shape_family_rule : CoverRule (ShapeFamily K) := by
  constructor
  · intro S T h inc B hb
    exact h B (hb.trans inc)
  · intro S T h e act incl B hb full
    let C := B.map e.symm.toEmbedding
    have into : C ⊆ T := by
      rintro _ hC
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hC
      exact incl i (hb hi)
    have hc := full_moves e.symm (action_symm act) full
    rcases h C into hc with ⟨i,ok⟩|⟨r,w,sz⟩
    · exact Or.inl ⟨i,.move e act ok⟩
    · refine Or.inr ⟨r,w.relabel e (act.rename K) (fun j hj ↦ ?_),by simpa [C] using sz⟩
      simpa [C] using hj

theorem no_line_family {T : Finset Cell} (h : ¬ContainsFullLine T) : ShapeFamily K T := by
  intro S sub full
  obtain ⟨axis,i,all⟩ := full
  exact (h ⟨axis,i,fun j ↦ sub (all j)⟩).elim

theorem shape_family_by_deletion (T : Finset Cell) (own : ShapeTest K T)
    (next : ∀ i ∈ T, ShapeFamily K (T.erase i)) : ShapeFamily K T := by
  intro S sub
  by_cases eq : S = T
  · simpa only [eq] using own
  · obtain ⟨j,hj,missing⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (Finset.card_lt_card (lt_of_le_of_ne sub eq))
    exact next j hj S (Finset.subset_erase.mpr ⟨sub,missing⟩)

theorem move_shape_family {S T : Finset Cell} (ht : ShapeFamily K T)
    (flip : Bool) (r c : Perm Idx) (inc : ∀ j ∈ S, moveCell flip r c j ∈ T) : ShapeFamily K S := by
  cases flip with
  | false => exact shape_family_rule.relabel ht (r.prodCongr c).symm (.rowCol r.symm c.symm) inc
  | true =>
    let e := Equiv.prodComm Idx Idx
    let B := S.map e.toEmbedding
    have hB : ShapeFamily K B := by
      apply shape_family_rule.relabel ht (r.prodCongr c).symm (.rowCol r.symm c.symm)
      rintro _ hb
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hb
      exact inc j hj
    exact shape_family_rule.relabel hB e.symm .transpose (fun j hj ↦ Finset.mem_map.mpr ⟨j,hj,rfl⟩)

theorem move_ambient {S T : Finset Cell} {d : ℕ} (h : AmbientWitness K S d)
    (flip : Bool) (r c : Perm Idx) (inc : ∀ j ∈ S, moveCell flip r c j ∈ T) : AmbientWitness K T d := by
  cases flip with
  | false => exact h.relabel (r.prodCongr c) (row_column_rename r c) inc
  | true =>
    let e := Equiv.prodComm Idx Idx
    have first : AmbientWitness K (S.map e.toEmbedding) d :=
      h.relabel e (transpose_rename) (fun i hi ↦ Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    apply first.relabel (r.prodCongr c) (row_column_rename r c)
    rintro _ hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
    exact inc i hi

#print axioms shape_family_rule
#print axioms move_ambient
end PermanentFive
