import Quantum.Hadamard.Basic

/-! Inflate the two-point orbits of a simultaneous involution on the rows and
columns of a sign matrix. Fixed indices stay single. A moving-to-moving
block has one value for equal labels and another for unequal labels. -/
namespace HadamardMod.InvolutionStretch
open Finset

abbrev Index (F P C : Type) := F ⊕ (P × C)

structure Blocks (m : ℕ) (F P : Type) where
  fixedFixed : F → F → ZMod m
  fixedPair : F → P → ZMod m
  pairFixed : P → F → ZMod m
  equal : P → P → ZMod m
  unequal : P → P → ZMod m

variable {m : ℕ} {F P : Type} [Fintype F] [Fintype P]

def index {C : Type} (i : F ⊕ P) (a : C) : Index F P C :=
  match i with
  | .inl f => .inl f
  | .inr u => .inr (u,a)

private theorem index_surjective {C : Type} [Inhabited C] (i : Index F P C) :
    ∃ (x : F ⊕ P) (a : C), index x a = i := by
  rcases i with f | ⟨p,c⟩
  · exact ⟨.inl f,default,rfl⟩
  · exact ⟨.inr p,c,rfl⟩

def Blocks.entry (B : Blocks m F P) {C : Type} [DecidableEq C] :
    RowMatrix m (Index F P C)
  | .inl i, .inl j => B.fixedFixed i j
  | .inl i, .inr (j,_) => B.fixedPair i j
  | .inr (i,_), .inl j => B.pairFixed i j
  | .inr (i,a), .inr (j,b) => if a=b then B.equal i j else B.unequal i j

private def fixedEntry (B : Blocks m F P) (i : F ⊕ P) (j : F) : ZMod m :=
  i.elim (fun f => B.fixedFixed f j) (fun p => B.pairFixed p j)

private def background (B : Blocks m F P) (i : F ⊕ P) (j : P) : ZMod m :=
  i.elim (fun f => B.fixedPair f j) (fun p => B.unequal p j)

private def correction (B : Blocks m F P) (i : F ⊕ P) (j : P) : ZMod m :=
  i.elim (fun _ => 0) (fun p => B.equal p j - B.unequal p j)

private theorem fixed_col (B : Blocks m F P) {C : Type} [DecidableEq C]
    (i : F ⊕ P) (a : C) (j : F) :
    B.entry (index i a) (.inl j) = fixedEntry B i j := by cases i <;> rfl

private theorem paired_col (B : Blocks m F P) {C : Type} [DecidableEq C]
    (i : F ⊕ P) (a : C) (j : P) (c : C) :
    B.entry (index i a) (.inr (j,c)) =
      background B i j + (if c=a then correction B i j else 0) := by
  cases i with
  | inl f => simp [Blocks.entry,index,background,correction]
  | inr p =>
    by_cases h : c=a
    · subst c; simp [Blocks.entry,index,background,correction]
    · simp [Blocks.entry,index,background,correction,h,Ne.symm h]

private theorem fiber_dot {C : Type} [Fintype C] [DecidableEq C] (a b : C)
    (x y u v : ZMod m) :
    (∑ c : C, (x+(if c=a then u else 0))*(y+(if c=b then v else 0))) =
      (Fintype.card C : ZMod m)*(x*y)+u*y+x*v+(if a=b then u*v else 0) := by
  have term (c : C) :
      (x+(if c=a then u else 0))*(y+(if c=b then v else 0)) =
        x*y+(if c=a then u*y else 0)+(if c=b then x*v else 0)+
        (if c=a then (if a=b then u*v else 0) else 0) := by
    by_cases h : c=a
    · subst c
      by_cases k : a=b <;> simp [k] <;> ring
    · by_cases k : c=b
      · subst b; simp [h]; ring
      · simp [h,k]
  simp [term,sum_add_distrib]

private theorem gram_transfer (B : Blocks m F P) {C D : Type}
    [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]
    (card : (Fintype.card C : ZMod m) = (Fintype.card D : ZMod m))
    (i j : F ⊕ P) (a b : C) (a' b' : D) (same : (a=b) ↔ (a'=b')) :
    (∑ z : Index F P C, B.entry (index i a) z * B.entry (index j b) z) =
    (∑ z : Index F P D, B.entry (index i a') z * B.entry (index j b') z) := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  simp only [fixed_col,Fintype.sum_prod_type,paired_col,fiber_dot,card]
  by_cases h : a=b
  · simp [h,same.mp h]
  · simp [h,mt same.mpr h]

private theorem entry_transfer (B : Blocks m F P) {C D : Type}
    [DecidableEq C] [DecidableEq D] (i j : F ⊕ P)
    (a b : C) (a' b' : D) (same : (a=b) ↔ (a'=b')) :
    B.entry (index i a) (index j b) = B.entry (index i a') (index j b') := by
  cases i <;> cases j <;> simp [Blocks.entry,index,same]

private theorem distinct_transfer {C D : Type} (i j : F ⊕ P)
    (a b : C) (a' b' : D) (same : (a=b) ↔ (a'=b'))
    (ne : index i a ≠ index j b) : index i a' ≠ index j b' := by
  cases i <;> cases j <;> simpa [index, same] using ne

/-- Replacing every moving pair by C gives a modular Hadamard matrix whenever
the number of labels is congruent to two modulo m. -/
theorem Blocks.inflate (B : Blocks m F P)
    (H : Good (B.entry (C:=Bool))) (C : Type) [Fintype C] [DecidableEq C] [Inhabited C]
    (card : (Fintype.card C : ZMod m)=2) : Good (B.entry (C:=C)) := by
  have agree (a b : C) : (a=b) ↔ (false = decide (a≠b)) := by by_cases h : a=b <;> simp [h]
  constructor
  · intro x y
    obtain ⟨i,a,rfl⟩ := index_surjective x
    obtain ⟨j,b,rfl⟩ := index_surjective y
    rw [entry_transfer B i j a b false _ (agree a b)]
    exact H.sign _ _
  · intro x y xy
    obtain ⟨i,a,rfl⟩ := index_surjective x
    obtain ⟨j,b,rfl⟩ := index_surjective y
    have e : (Fintype.card C : ZMod m) = (Fintype.card Bool : ZMod m) := by simpa using card
    rw [gram_transfer B e i j a b false _ (agree a b)]
    exact H.ortho _ _ (distinct_transfer i j a b false _ (agree a b) xy)

#print axioms Blocks.inflate
end HadamardMod.InvolutionStretch
