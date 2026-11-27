import HollowGridFactor
import PermanentWitnesses

/-! The Hessian of the permanent is hollow in the two coordinate directions
and invariant under the two independent exchanges of row and column indices. -/
noncomputable section
open Finset MvPolynomial Equiv Matrix QuinticPencil
namespace PermanentFive
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

private theorem second_col_swap (z : I × I → K) (r s i j : I) :
    secondAt z (r,i) (s,j) = secondAt z (r,j) (s,i) := by
  classical
  by_cases hij : i=j
  · subst j
    rfl
  unfold secondAt
  apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j))
  intro p
  change (if p j=s ∧ i≠j ∧ p i=r then _ else 0) =
    (if (p*Equiv.swap i j) i=s ∧ j≠i ∧ (p*Equiv.swap i j) j=r then _ else 0)
  simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_left,Equiv.swap_apply_right]
  by_cases h : p j=s ∧ p i=r
  · rw [ite_eq_left ⟨h.1,hij,h.2⟩,ite_eq_left ⟨h.1,Ne.symm hij,h.2⟩]
    rw [Finset.erase_right_comm]
    apply Finset.prod_congr rfl
    intro k hk
    have ne := Finset.mem_erase.mp hk
    have ne' := Finset.mem_erase.mp ne.2
    change z (p k,k)=z (p (Equiv.swap i j k),k)
    rw [Equiv.swap_apply_of_ne_of_ne ne'.1 ne.1]
  · simp [hij,Ne.symm hij,h]

theorem hessian_grid_symmetry (z : I × I → K) :
    HollowGrid.PairSymmetric (hessian (per K I) z) := by
  constructor
  · intro r i j
    rw [second_formula,secondAt]
    apply Finset.sum_eq_zero
    intro p _
    have no : ¬(p j=r ∧ i≠j ∧ p i=r) := fun h ↦ h.2.1 (p.injective (h.2.2.trans h.1.symm))
    simpa only [ite_eq_right_iff] using fun h ↦ (no h).elim
  · intro i r s
    simp [second_formula,secondAt]
  · intro r s i j
    calc hessian (per K I) z (r,i) (s,j) = hessian (per K I) z (s,j) (r,i) := by
          change MvPolynomial.eval z (pderiv _ (pderiv _ _))=_
          rw [pderiv_comm]
          rfl
         _ = _ := by rw [second_formula,second_formula,second_col_swap]
  · intro r s i j
    rw [second_formula,second_formula,second_col_swap]

#print axioms hessian_grid_symmetry
end PermanentFive
