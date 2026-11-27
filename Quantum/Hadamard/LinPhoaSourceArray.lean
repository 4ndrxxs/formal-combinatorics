import Quantum.Hadamard.ProjectiveSplitComparison

/-! The literal two-row bordering of Lin and Phoa (2016), equation (3.1),
applied to the signed sets in Momihara, Suda and Xiang (2022), Theorem 4.1. -/

noncomputable section
open Finset Matrix Hadamard.NearBorder
namespace Hadamard.LinPhoa

variable {m : ℕ} [NeZero m]

def orientation (c : Bool) : ℝ := if c then 1 else -1

def strip : Matrix Bool Bool ℝ := fun a b ↦ if a && b then -1 else 1

def corner (c : Bool) : Matrix Bool Bool ℝ := fun a b ↦ orientation c*strip a b

def core (f : Bool → Fin m → ℝ) : Matrix (Core m) (Core m) ℝ
  | (false,k),(false,l) => f false (l-k)
  | (false,k),(true,l) => f true (l-k)
  | (true,k),(false,l) => f true (k-l)
  | (true,k),(true,l) => -f false (k-l)

/-- In border-first order the block rows are
(c,c,1,1), (c,-c,1,-1), (1,1,A,B), (1,-1,Bᵀ,-Aᵀ). -/
def array (c : Bool) (f : Bool → Fin m → ℝ) := bordered (core f) strip strip (corner c)

def layout (m : ℕ) [NeZero m] : CyclicLayout m where
  order a := if a then Equiv.swap false true else Equiv.refl Bool
  change a b := { offset := 0, reversed := a, scale := strip a b,
                  unit := by cases a <;> cases b <;> norm_num [strip] }

theorem layout_core (f : Bool → Fin m → ℝ) : (layout m).core f=core f := by
  ext ⟨a,k⟩ ⟨b,l⟩
  cases a <;> cases b <;> simp [CyclicLayout.core,layout,SequenceChange.apply,core,strip]

theorem strip_sign : Signs strip := by intro a b; cases a <;> cases b <;> norm_num [strip]
theorem corner_sign (c : Bool) : Signs (corner c) := by
  intro a b; cases a <;> cases b <;> cases c <;> norm_num [corner,orientation,strip]

def gram (c : Bool) (f : Bool → Fin m → ℝ) := array c f*(array c f).transpose

omit [NeZero m] in
private theorem gram_sym (c : Bool) (f : Bool → Fin m → ℝ) (i j : Index m) :
    gram c f i j=gram c f j i := by simp [gram,Matrix.mul_apply,mul_comm]

private theorem reflected_product (f g : Fin m → ℝ) (k l : Fin m) :
    (∑ t, f (t-k)*g (l-t))=∑ t,g (t-k)*f (l-t) := by
  have eq := (Equiv.subLeft (k+l)).sum_comp (fun t : Fin m ↦ g (t-k)*f (l-t))
  change (∑ t, g (k+l-t-k)*f (l-(k+l-t)))=_ at eq
  have e (t : Fin m) : k+l-t-k=l-t := by abel
  have e' (t : Fin m) : l-(k+l-t)=t-k := by abel
  simpa only [e,e',mul_comm] using eq

/-- The upper and lower block rows of the complete array are orthogonal. -/
theorem bulk_cross (c : Bool) (f : Bool → Fin m → ℝ) (k l : Fin m) :
    gram c f (bulk false k) (bulk true l)=0 := by
  simp only [gram,array,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_sum_type,
    Fintype.sum_prod_type,Fintype.sum_bool,bulk,bordered,core]
  simp only [strip,Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,ite_true,
    mul_neg,sum_neg_distrib,one_mul]
  rw [reflected_product (f false) (f true) k l]
  ring

omit [NeZero m] in
private theorem rim_cross (c : Bool) (f : Bool → Fin m → ℝ) :
    gram c f (rim false) (rim true)=0 := by
  cases c <;> simp [gram,array,Matrix.mul_apply,bordered,rim,Fintype.sum_sum_type,
    Fintype.sum_prod_type,strip,corner,orientation]

private theorem mixed (c : Bool) (f : Bool → Fin m → ℝ) (r : ℝ) (sr : (∑t,f false t)=r)
    (sz : (∑t,f true t)=0) (a b : Bool) (k : Fin m) :
    gram c f (bulk a k) (rim b)=
      (if a then -r*strip b true else r) + (if a=b then 2*orientation c else 0) := by
  have ar (v : Bool) : (∑t, f v (t-k))=∑ t, f v t := (Equiv.subRight k).sum_comp (f v)
  have rev (v : Bool) : (∑t, f v (k-t))=∑ t, f v t := (Equiv.subLeft k).sum_comp (f v)
  cases a <;> cases b <;>
    simp [gram,array,Matrix.mul_apply,bordered,bulk,rim,Fintype.sum_sum_type,Fintype.sum_prod_type,
      core,strip,corner,ar,rev,sr,sz]
  ring

#print axioms bulk_cross


open Hadamard.MSXCore

def classOf (i : Bool) : Index m → Bool
  | .inl (a,_) => a
  | .inr b => if i then b else !b

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The two-class Gram partition of the literal published array is derived
from the four source sets, for every allowed corner sign. -/
def source_partition (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j c : Bool) (valid : i=true ∨ c=true)
    (e : Fin m ≃ SquareIndex F) (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) :
    Partition (gram c (sourcePair w i j e)) := by
  let f := sourcePair w i j e
  have sums := source_pair_sums hc q4 w hw i j e
  have old (a : Bool) (k l : Fin m) (ne : k≠l) :
      gram c f (bulk a k) (bulk a l)=2 ∨ gram c f (bulk a k) (bulk a l)= -2 := by
    have diff : (e k).val≠(e l).val := fun h ↦ ne (e.injective (Subtype.ext h))
    have gl : gram c f (bulk a k) (bulk a l)=(incidenceGram w i j (e k).val (e l).val:ℝ)+2 := by
      have left := bulk_gram (core f) strip strip (corner c) strip_sign a k l
      have right := source_layout_gram w i j e cyc (layout m) a k l
      rw [layout_core] at right
      exact left.trans (congrArg (·+2) right)
    rw [gl,incidence_gram hc q4 hw (e k).property (e l).property,ite_eq_right diff]
    rcases quadraticChar_dichotomy (sub_ne_zero.mpr (Ne.symm diff)) with v|v <;>
      cases i <;> norm_num [cosetSign,v]
  have perpendicular (a b : Bool) (k l : Fin m) (ne : a≠b) :
      gram c f (bulk a k) (bulk b l)=0 := by
    cases a <;> cases b
    · exact (ne rfl).elim
    · exact bulk_cross c f _ _
    · rw [gram_sym]; exact bulk_cross c f _ _
    · exact (ne rfl).elim
  have border (a : Bool) (k : Fin m) (b : Bool) :
      (classOf i (bulk a k)=classOf (m:=m) i (rim b) →
        gram c f (bulk a k) (rim b)=2 ∨ gram c f (bulk a k) (rim b)= -2) ∧
      (classOf i (bulk a k)≠classOf (m:=m) i (rim b) → gram c f (bulk a k) (rim b)=0) := by
    rw [mixed c f _ sums.1 sums.2]
    cases i <;> cases c <;> cases a <;> cases b <;>
      simp at valid <;> norm_num [classOf,bulk,rim,orientation,strip]
  refine { part := classOf i, count := ?_, inside := ?_, outside := ?_ }
  · intro b
    simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
    cases i <;> cases b <;> simp [classOf]
  · rintro (⟨a,k⟩|a) (⟨b,l⟩|b) ne eq
    · change a=b at eq; subst b
      exact old a k l (fun z ↦ ne (by rw [z]))
    · exact (border a k b).1 eq
    · change gram c f (rim a) (bulk b l)=2 ∨ gram c f (rim a) (bulk b l)= -2
      rw [gram_sym c f (rim a) (bulk b l)]
      exact (border b l a).1 eq.symm
    · cases i <;> cases a <;> cases b <;> simp_all [classOf]
  · rintro (⟨a,k⟩|a) (⟨b,l⟩|b) ne
    · exact perpendicular a b k l ne
    · exact (border a k b).2 ne
    · rw [gram_sym]; exact (border b l a).2 (Ne.symm ne)
    · cases a <;> cases b
      · exact (ne rfl).elim
      · exact rim_cross c f
      · rw [gram_sym]; exact rim_cross c f
      · exact (ne rfl).elim

/-- Among the two choices of corner in equation (3.1), the displayed
conditions on the support index and the corner sign are also necessary. -/
theorem source_partition_iff (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (w : F) (hw : quadraticChar F w= -1) (i j c : Bool) (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val=(e k).val/(e l).val) :
    Nonempty (Partition (gram c (sourcePair w i j e))) ↔ i=true ∨ c=true := by
  refine ⟨?_,fun valid ↦ ⟨source_partition hc q4 w hw i j c valid e cyc⟩⟩
  rintro ⟨p⟩
  by_cases hi : i=true
  · exact Or.inl hi
  by_cases hc' : c=true
  · exact Or.inr hc'
  have fi : i=false := by cases i <;> simp_all
  have fc : c=false := by cases c <;> simp_all
  subst i; subst c
  exfalso
  let f := sourcePair w false j e
  let k : Fin m := 0
  have sums := source_pair_sums hc q4 w hw false j e
  have wrong : gram false f (bulk false k) (rim false)= -4 := by
    rw [mixed false f _ sums.1 sums.2]; norm_num [orientation]
  by_cases eq : p.part (bulk false k)=p.part (rim false)
  · rcases p.inside (bulk false k) (rim false) (by simp [bulk,rim]) eq with v|v <;>
      change gram false f (bulk false k) (rim false)=_ at v <;> linarith
  · have v := p.outside _ _ eq
    change gram false f (bulk false k) (rim false)=0 at v
    linarith

omit [NeZero m] in
/-- Every entry in the displayed array is a sign, for either corner. -/
theorem source_entry_sign (w : F) (i j c : Bool) (e : Fin m ≃ SquareIndex F)
    (a b : Index m) : array c (sourcePair w i j e) a b=1 ∨ array c (sourcePair w i j e) a b= -1 := by
  classical
  have inc (s : F) (v : Bool) (t : F) : (incidence s v t:ℝ)^2=1 := by
    unfold incidence; split <;> norm_num
  have h : (array c (sourcePair w i j e) a b)^2=1 := by
    cases a with
    | inl a =>
      rcases a with ⟨a,k⟩
      cases b with
      | inl b =>
        rcases b with ⟨b,l⟩
        cases a <;> cases b <;> simp only [array,bordered,core,sourcePair,neg_sq] <;> apply inc
      | inr b => exact strip_sign a b
    | inr a =>
      cases b with
      | inl b => exact strip_sign a b.1
      | inr b => exact corner_sign c a b
  exact sq_eq_one_iff.mp h

#print axioms source_entry_sign
#print axioms source_partition
#print axioms source_partition_iff

end Hadamard.LinPhoa
