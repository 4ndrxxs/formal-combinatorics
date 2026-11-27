import HollowGridSmallRank
import PermanentHessianSymmetry
import PencilHomogeneousRank

/-! The rank gap applies to the Hessian of every square permanent. For a
size-21 expression of the order-five permanent it restricts every point
in the actual endpoint kernel. -/
noncomputable section
open Matrix Module QuinticPencil
namespace PermanentFive
variable {K I n : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n]

theorem permanent_hessian_rank_gap (z : I × I → K) :
    (hessian (per K I) z).rank=0 ∨ (hessian (per K I) z).rank=4 ∨
    6≤(hessian (per K I) z).rank :=
  HollowGrid.rank_gap _ (hessian_grid_symmetry z)

theorem permanent_hessian_small (z : I × I → K) (hn : hessian (per K I) z ≠ 0)
    (hr : (hessian (per K I) z).rank≤5) :
    (hessian (per K I) z).rank=4 ∧ ∃ (R S C D : I → K), ∀ r s i j,
      hessian (per K I) z (r,i) (s,j)=(R r*S s+S r*R s)*(C i*D j+D i*C j) :=
  HollowGrid.small_factorization _ (hessian_grid_symmetry z) hn hr

theorem endpoint_hessian_bound [CharZero K] (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (size : Fintype.card n=20)
    (z : Cell → K) (hz : z ∈ (endpoints b c).ker) :
    5+(hessian (per K Idx) z).rank ≤ finrank K (endpoints b c).ker := by
  have h := (normalized_partial_kernel (per_homogeneous K Idx) b c D rep z hz).2
  change 25+(hessian (per K Idx) z).rank ≤ Fintype.card n + finrank K (endpoints b c).ker at h
  omega

theorem endpoint_eight_zero [CharZero K] (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (size : Fintype.card n=20)
    (small : finrank K (endpoints b c).ker≤8) (z : Cell → K) (hz : z ∈ (endpoints b c).ker) :
    hessian (per K Idx) z=0 := by
  by_contra hn
  have bound := endpoint_hessian_bound b c D rep size z hz
  have r := (permanent_hessian_small z hn (by omega)).1
  omega

theorem endpoint_ten_forms [CharZero K] (b c : n → Cell → K) (M : n → n → Cell → K)
    (rep : per K Idx = regularDet b c M) (size : Fintype.card n=20)
    (small : finrank K (endpoints b c).ker≤10) (z : Cell → K) (hz : z ∈ (endpoints b c).ker) :
    hessian (per K Idx) z=0 ∨ ((hessian (per K Idx) z).rank=4 ∧ ∃ (R S C D : Idx → K),
      ∀ r s i j, hessian (per K Idx) z (r,i) (s,j)=(R r*S s+S r*R s)*(C i*D j+D i*C j)) := by
  by_cases hn : hessian (per K Idx) z=0
  · exact Or.inl hn
  have bound := endpoint_hessian_bound b c M rep size z hz
  exact Or.inr (permanent_hessian_small z hn (by omega))

#print axioms permanent_hessian_rank_gap
#print axioms permanent_hessian_small
#print axioms endpoint_eight_zero
#print axioms endpoint_ten_forms
end PermanentFive
