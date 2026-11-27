import PermanentWeightedPoint
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow.Weighted
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
abbrev Words (I : Type*) := Multiset (Multiset (CellOf I))
def evalWords (z : CellOf I → R) (a : Words I) : R := (a.map fun w ↦ (w.map z).prod).sum
def word (p : Perm I) (s : Finset I) : Multiset (CellOf I) := s.val.map fun j ↦ (p j,j)
def secondWords (e f : CellOf I) : Words I :=
  (univ.filter fun p : Perm I ↦ p f.2=f.1 ∧ e.2≠f.2 ∧ p e.2=e.1).val.map
    fun p ↦ word p ((univ.erase f.2).erase e.2)
def firstWords (e : CellOf I) : Words I :=
  (univ.filter fun p : Perm I ↦ p e.2=e.1).val.map fun p ↦ word p (univ.erase e.2)
theorem second_eval (z : CellOf I → R) (e f : CellOf I) :
    hessian (per R I) z e f=evalWords z (secondWords e f) := by
  rw [second_formula,secondAt,←Finset.sum_filter]
  simp [evalWords,secondWords,word,Finset.sum,Finset.prod]
theorem first_eval (z : CellOf I → R) (e : CellOf I) : gradAt z e=evalWords z (firstWords e) := by
  rw [gradAt,←Finset.sum_filter]
  simp [evalWords,firstWords,word,Finset.sum,Finset.prod]
end PermanentArrow.Weighted
