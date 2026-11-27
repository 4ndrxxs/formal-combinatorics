module

public import Quantum.Sudoku

/-! Exact reconstruction from complete prescribed blocks. In any size, a pattern
    determines every completable instance uniquely iff its missing block positions
    form a matching between the bands and stacks. Uniqueness is of projectors. -/
@[expose] public section
noncomputable section
namespace QuantumSudoku
namespace Blocks
open Finset InnerProductSpace
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Operator (I : Type*) [Fintype I] := H I →L[ℂ] H I
def projector (x : H I) : Operator I := rankOne ℂ x x
def cell (v : Grid I) (r c : Index I) : Operator I := projector (v r c)

omit [DecidableEq I] in
private theorem line_sum {v : Index I → H I} (h : BasisLine v) :
    ∑ i, projector (v i) = 1 := by
  obtain ⟨b,rfl⟩ := h
  exact b.sum_rankOne_eq_id

private theorem line_mul {v : Index I → H I} (h : BasisLine v) (p q : Index I) :
    projector (v p)*projector (v q) = if p=q then projector (v p) else 0 := by
  obtain ⟨b,rfl⟩ := h
  change rankOne ℂ (b p) (b p) ∘L rankOne ℂ (b q) (b q) = _
  rw [rankOne_comp_rankOne,b.inner_eq_ite]
  by_cases hp : p=q <;> simp [hp,projector]

def rowPart (v : Grid I) (r : Index I) (j : I) : Operator I := ∑ b, cell v r (j,b)
def colPart (v : Grid I) (i : I) (c : Index I) : Operator I := ∑ a, cell v (i,a) c

theorem reconstruct {v : Grid I} (hv : Valid v) (i j a b : I) :
    rowPart v (i,a) j * colPart v i (j,b) = cell v (i,a) (j,b) := by
  simp only [rowPart,colPart,sum_mul,mul_sum]
  have prod (c d : I) : cell v (i,a) (j,c) * cell v (i,d) (j,b) =
      if (a,c)=(d,b) then cell v (i,a) (j,c) else 0 :=
    line_mul (hv.block i j) (a,c) (d,b)
  simp_rw [prod]
  rw [sum_eq_single a]
  · simp [Prod.mk.injEq]
  · intro d _ hd
    simp [Prod.mk.injEq,Ne.symm hd]
  · simp

def Matching (missing : Set (Index I)) : Prop :=
  (∀ i j k, (i,j)∈missing → (i,k)∈missing → j=k) ∧
  (∀ i j k, (i,k)∈missing → (j,k)∈missing → i=j)

def Determines (missing : Set (Index I)) : Prop :=
  ∀ v w : Grid I, Valid v → Valid w →
    (∀ r c : Index I, (r.1,c.1)∉missing → cell v r c = cell w r c) →
    ∀ r c, cell v r c = cell w r c

omit [DecidableEq I] in
private theorem one_remainder {A : Type*} [AddCommGroup A] (f g : I → A) (i : I)
    (t : ∑ j, f j = ∑ j, g j) (h : ∀ j, j≠i → f j=g j) : f i=g i := by
  have z : (∑ j, (f j-g j)) = 0 := by rw [sum_sub_distrib,t,sub_self]
  have only : (∑ j, (f j-g j)) = f i-g i :=
    sum_eq_single i (by intro j _ hj; rw [h j hj,sub_self]) (by simp)
  exact sub_eq_zero.mp (only.symm.trans z)

theorem matching_determines {missing : Set (Index I)} (hm : Matching missing) :
    Determines missing := by
  intro v w hv hw agree
  rintro ⟨i,a⟩ ⟨j,b⟩
  by_cases hij : (i,j)∈missing
  · have hr (s : Grid I) (hs : Valid s) : ∑ x, rowPart s (i,a) x = 1 := by
      simpa only [Fintype.sum_prod_type,rowPart,cell] using line_sum (hs.row (i,a))
    have hc (s : Grid I) (hs : Valid s) : ∑ x, colPart s x (j,b) = 1 := by
      simpa only [Fintype.sum_prod_type,colPart,cell] using line_sum (hs.column (j,b))
    have roweq := one_remainder (rowPart v (i,a)) (rowPart w (i,a)) j
      ((hr v hv).trans (hr w hw).symm) (by
        intro k hk
        exact sum_congr rfl (fun d _ => agree (i,a) (k,d) (fun h => hk (hm.1 i k j h hij))))
    have coleq := one_remainder (fun x => colPart v x (j,b)) (fun x => colPart w x (j,b)) i
      ((hc v hv).trans (hc w hw).symm) (by
        intro k hk
        exact sum_congr rfl (fun d _ => agree (k,d) (j,b) (fun h => hk (hm.2 k i j h hij))))
    rw [← reconstruct hv i j a b, ← reconstruct hw i j a b,roweq,coleq]
  · exact agree _ _ hij

def transpose (v : Grid I) : Grid I := fun r c => v c r

theorem transpose_valid [Nonempty I] {v : Grid I} (hv : Valid v) : Valid (transpose v) := by
  refine ⟨hv.column,hv.row,?_⟩
  intro i j
  apply basis_of_gram
  obtain ⟨b,hb⟩ := hv.block j i
  rintro ⟨a,c⟩ ⟨d,e⟩
  have h := b.inner_eq_ite (c,a) (e,d)
  rw [congrFun hb (c,a),congrFun hb (e,d)] at h
  simpa [transpose,Prod.mk.injEq,and_comm] using h

private theorem trans_determines [Nonempty I] {missing : Set (Index I)}
    (h : Determines missing) : Determines {u | (u.2,u.1) ∈ missing} := by
  intro v w hv hw agree r c
  exact h (transpose v) (transpose w) (transpose_valid hv) (transpose_valid hw)
    (fun u t hn => agree t u hn) c r

private theorem point_inj : Function.Injective (fun i : Index I => projector (point i)) := by
  intro i j h
  by_contra hij
  have e := congrArg (fun T : Operator I => inner ℂ (point i) (T (point i))) h
  simp [projector,rankOne_apply,inner_smul_right,point_inner,Ne.symm hij] at e
  have ei := congrArg (fun v : H I => v i) e
  simp at ei

variable [AddCommGroup I]

def labelled (σ : I → Equiv.Perm I) : Grid I :=
  fun r c => point (r.2+σ r.1 c.1,r.1+c.2)

theorem labelled_valid (σ : I → Equiv.Perm I) : Valid (labelled σ) := by
  constructor
  · rintro ⟨i,a⟩
    apply basis_of_gram
    rintro ⟨j,b⟩ ⟨k,c⟩
    simp only [labelled,point_inner,Prod.mk.injEq,add_right_inj,Equiv.apply_eq_iff_eq]
  · rintro ⟨j,b⟩
    apply basis_of_gram
    rintro ⟨i,a⟩ ⟨k,c⟩
    simp only [labelled,point_inner,Prod.mk.injEq,add_left_inj]
    by_cases h : i=k <;> simp [h]
  · intro i j
    apply basis_of_gram
    rintro ⟨a,b⟩ ⟨x,y⟩
    simp only [labelled,point_inner,Prod.mk.injEq,add_right_inj,add_left_inj]

private theorem at_most_one_in_band {missing : Set (Index I)} (h : Determines missing)
    (i j k : I) (hj : (i,j)∈missing) (hk : (i,k)∈missing) : j=k := by
  by_contra hne
  let σ (x : I) := if x=i then Equiv.swap j k else Equiv.refl I
  let idp (_ : I) := Equiv.refl I
  have agree (r c : Index I) (known : (r.1,c.1)∉missing) :
      cell (labelled σ) r c = cell (labelled idp) r c := by
    by_cases hi : r.1=i
    · have nj : c.1≠j := fun e => known (by simpa [hi,e] using hj)
      have nk : c.1≠k := fun e => known (by simpa [hi,e] using hk)
      simp [cell,labelled,σ,idp,hi,Equiv.swap_apply_of_ne_of_ne nj nk]
    · simp [cell,labelled,σ,idp,hi]
  have diff := h _ _ (labelled_valid σ) (labelled_valid idp) agree (i,0) (j,0)
  apply hne
  have label := point_inj diff
  simpa [labelled,σ,idp] using (congrArg Prod.fst label).symm

theorem determines_iff_matching (missing : Set (Index I)) :
    Determines missing ↔ Matching missing := by
  refine ⟨fun h => ⟨at_most_one_in_band h,?_⟩,matching_determines⟩
  intro i j k hi hj
  exact at_most_one_in_band (trans_determines h) k i j hi hj

#print axioms reconstruct
#print axioms determines_iff_matching
end Blocks
end QuantumSudoku
