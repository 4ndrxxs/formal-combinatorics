import PermanentArrowLeaf

/-! The Hessian of the arrow matrix has entries determined entirely by
equalities among two row indices, two column indices, and the center. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow
variable {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [CommRing R]

def point (R : Type*) [CommRing R] (c : I) (e : CellOf I) : R :=
  if e=(c,c) then 1-(Fintype.card I:R) else
    if e.1=c ∨ e.2=c ∨ e.1=e.2 then 1 else 0

def other (c a b : I) := if a=c then b else a

omit [Fintype I] [Fintype J] in
theorem other_equiv (b : I ≃ J) (c a d : I) : other (b c) (b a) (b d)=b (other c a d) := by
  by_cases h : a=c <;> simp [other,h]

omit [Fintype I] in
theorem other_some (c a d : I) : other (some c) (some a) (some d)=some (other c a d) := by
  by_cases h : a=c <;> simp [other,h]

def entry (c : I) (e f : CellOf I) : ℤ :=
  if e.1=f.1 ∨ e.2=f.2 then 0 else
  let r := other c e.1 f.1
  let j := other c e.2 f.2
  if e.1=c ∨ f.1=c then
    if e.2=c ∨ f.2=c then (if r=j then 1 else 0)
    else if r=e.2 ∨ r=f.2 then 1 else 0
  else if e.2=c ∨ f.2=c then
    if j=e.1 ∨ j=f.1 then 1 else 0
  else if (e.1=e.2 ∧ f.1=f.2) ∨ (e.1=f.2 ∧ f.1=e.2) then -2
  else if e.1=e.2 ∨ f.1=f.2 ∨ e.1=f.2 ∨ f.1=e.2 then 1 else 0

theorem leaf_point (c : I) : leaf c (point R c)=point R (some c) := by
  funext ⟨i,j⟩
  cases i with
  | none => cases j <;> simp [leaf,point]
  | some i =>
    cases j with
    | none => simp [leaf,point]
    | some j =>
      by_cases h : i=c <;> by_cases k : j=c <;> simp [leaf,lower,point,h,k]

omit [Fintype I] in
theorem leaf_entry (c : I) (e f : CellOf I) :
    entry (some c) (old e) (old f)=entry c e f := by
  rcases e with ⟨a,b⟩
  rcases f with ⟨i,j⟩
  simp [entry,old,other_some]

theorem point_equiv (b : I ≃ J) (c : I) :
    point R c ∘ (b.prodCongr b).symm=point R (b c) := by
  funext ⟨i,j⟩
  obtain ⟨a,rfl⟩ := b.surjective i
  obtain ⟨d,rfl⟩ := b.surjective j
  simp [point,Prod.ext_iff,Fintype.card_congr b]

omit [Fintype I] [Fintype J] in
theorem entry_equiv (b : I ≃ J) (c : I) (e f : CellOf I) :
    entry (b c) (b.prodCongr b e) (b.prodCongr b f)=entry c e f := by
  rcases e with ⟨a,d⟩
  rcases f with ⟨i,j⟩
  change entry (b c) (b a,b d) (b i,b j)=_
  simp [entry,other_equiv]

theorem point_cast (K : Type*) [Field K] (c : I) : point K c=castPoint K (point ℤ c) := by
  funext e
  by_cases h : e=(c,c) <;> by_cases k : e.1=c ∨ e.2=c ∨ e.1=e.2 <;>
    simp [point,castPoint,h,k]

#print axioms leaf_point
end PermanentArrow
