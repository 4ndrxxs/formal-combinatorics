import PermanentWitnesses
import Mathlib.GroupTheory.Perm.Option

/-! Exact bordered expansion of the permanent over an arbitrary
commutative ring. A permutation either fixes the new index, or inserts
it between a column and the old row matched to that column. -/
noncomputable section
open Matrix Equiv Finset PermanentFive
namespace PermanentBorder
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

def core (M : Matrix (Option I) (Option I) R) : Matrix I I R := M.submatrix some some
def inside (M : Matrix (Option I) (Option I) R) (u : I × I) := M (some u.1) (some u.2)

private theorem fixed_term (M : Matrix (Option I) (Option I) R) (p : Perm I) :
    (∏ k, M (Perm.decomposeOption.symm (none,p) k) k) =
      M none none * ∏ k, M (some (p k)) (some k) := by
  rw [Fintype.prod_option]
  simp

private theorem moved_term (M : Matrix (Option I) (Option I) R) (r : I) (p : Perm I) :
    (∏ k, M (Perm.decomposeOption.symm (some r,p) k) k) =
      M (some r) none*M none (some (p.symm r)) *
        ∏ k ∈ univ.erase (p.symm r), M (some (p k)) (some k) := by
  let e := Perm.decomposeOption.symm (some r,p)
  have first : e none=some r := by simp [e,Perm.decomposeOption_symm_apply]
  have next : e (some (p.symm r))=none := by simp [e,Perm.decomposeOption_symm_apply]
  have rest (k : I) (ne : k≠p.symm r) : e (some k)=some (p k) := by
    have pr : p k≠r := fun eq ↦ ne (by rw [←eq,p.symm_apply_apply])
    simp [e,Perm.decomposeOption_symm_apply,Equiv.swap_apply_def,pr]
  change (∏ k, M (e k) k)=_
  rw [Fintype.prod_option,first,←Finset.mul_prod_erase univ (fun k : I ↦ M (e (some k)) (some k))
    (mem_univ (p.symm r)),next,mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro k hk
  rw [rest k (mem_erase.mp hk).1]

theorem permanent_border (M : Matrix (Option I) (Option I) R) :
    M.permanent=M none none*(core M).permanent+
      ∑ r : I, ∑ j : I, M (some r) none * M none (some j) * gradAt (inside M) (r,j) := by
  unfold Matrix.permanent
  rw [←Perm.decomposeOption.symm.sum_comp (fun p : Perm (Option I) ↦ ∏ k, M (p k) k),
    Fintype.sum_prod_type,Fintype.sum_option]
  congr 1
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ ↦ fixed_term M p)
  · apply Finset.sum_congr rfl
    intro r _
    simp only [gradAt,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [moved_term,Finset.sum_eq_single (p.symm r)]
    · simp [inside]
    · intro j _ ne
      have pr : p j≠r := fun eq ↦ ne (by rw [←eq,p.symm_apply_apply])
      simp [pr]
    · simp

#print axioms permanent_border
end PermanentBorder
