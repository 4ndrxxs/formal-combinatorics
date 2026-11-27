import PermanentWeightedLeaf
import PermanentArrowRank

/-! Weighted arrow points and their first and second derivatives. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow.Weighted
variable {R I J : Type*} [CommRing R] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def total (c : I) (s : I→R) := ∑ i, if i=c then 0 else s i
def prodAll (c : I) (s : I→R) := ∏ i, if i=c then 1 else s i
def skip (c i : I) (s : I→R) := ∏ j, if j=c ∨ j=i then 1 else s j

def board (c : I) (s : I→R) (e : CellOf I) : R :=
  if e.1=c then (if e.2=c then -total c s else s e.2)
  else if e.2=c ∨ e.1=e.2 then s e.1 else 0

def rowJet (c i j : I) (s : I→R) (v : CellOf I) : R :=
  hessian (per R I) (board c s) (i,j) v-hessian (per R I) (board c s) (i,c) v-
    hessian (per R I) (board c s) (c,j) v+hessian (per R I) (board c s) (c,c) v

def firstJet (c i j : I) (s : I→R) : R :=
  gradAt (board c s) (i,j)-gradAt (board c s) (i,c)-gradAt (board c s) (c,j)+gradAt (board c s) (c,c)

def Law (c i j : I) (s : I→R) (v : CellOf I) : Prop :=
  gradAt (board c s) (c,c)=prodAll c s ∧ firstJet c i j s=0 ∧
    rowJet c i j s v=(if v=(j,i) then -2*(skip c i s+skip c j s) else 0)

theorem leaf_board (c : I) (s : Option I→R) :
    leaf (s none) c (board c (s ∘ some))=board (some c) s := by
  funext ⟨i,j⟩
  cases i with
  | none => cases j <;> simp [leaf,board,eq_comm]
  | some i =>
    cases j with
    | none => simp [leaf,board]
    | some j =>
      by_cases a : i=c <;> by_cases b : j=c <;>
        simp [leaf,lower,board,total,Fintype.sum_option,a,b]
      ring

theorem leaf_law (c i j : I) (s : Option I→R) (v : CellOf I) (h : Law c i j (s ∘ some) v) :
    Law (some c) (some i) (some j) s (old v) := by
  obtain ⟨hc,hf,hr⟩ := h
  have g (a b : I) :
      gradAt (board (some c) s) (some a,some b)=s none*gradAt (board c (s ∘ some)) (a,b) := by
    rw [←leaf_board]
    exact leaf_gradient _ _ _ (a,b)
  have q (a b : I) :
      hessian (per R (Option I)) (board (some c) s) (some a,some b) (old v)=
      s none*hessian (per R I) (board c (s ∘ some)) (a,b) v := by
    rw [←leaf_board]
    exact leaf_hessian _ _ _ (a,b) v
  refine ⟨?_,?_,?_⟩
  · rw [g,hc]
    simp [prodAll,Fintype.prod_option]
  · unfold firstJet at hf ⊢
    simp only [g]
    linear_combination s none*hf
  · unfold rowJet at hr ⊢
    simp only [q]
    have sk (a : I) : skip (some c) (some a) s=s none*skip c a (s ∘ some) := by
      simp [skip,Fintype.prod_option]
    rw [sk,sk]
    by_cases e : v=(j,i)
    · subst v
      simp only [ite_true] at hr
      change _=(if old (j,i)=old (j,i) then _ else _)
      rw [ite_eq_left rfl]
      linear_combination s none*hr
    · have ne : old v≠(some j,some i) := old_inj.ne e
      simp only [e,ne,ite_false] at hr ⊢
      linear_combination s none*hr

end PermanentArrow.Weighted
