import HollowGridDisjoint
import Mathlib.Data.ZMod.Basic

/-! A binary example with three mutually adjacent row indices shows why
the disjoint-support refinement requires characteristic different from two. -/
noncomputable section
open Matrix
namespace HollowGrid
def binaryTriangle : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) (ZMod 2) := Matrix.of fun u v ↦
  if u.1≠v.1 ∧ u.2≠v.2 then 1 else 0

private theorem binary_pair : PairSymmetric binaryTriangle := by
  constructor <;> decide +kernel

theorem binary_triangle_rank : binaryTriangle.rank=4 := by
  have h : binaryTriangle≠0 := by
    intro eq
    have q := congrArg (fun A : Matrix (Fin 3×Fin 2) (Fin 3×Fin 2) (ZMod 2) ↦ A (0,0) (1,1)) eq
    exact (by decide : binaryTriangle (0,0) (1,1)≠0) q
  apply (rank_four_iff binaryTriangle binary_pair h).2
  refine ⟨![1,0,1],![0,1,1],![1,0],![0,1],?_⟩
  decide +kernel

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 10000 in
theorem binary_triangle_overlaps :
    ¬ ∃ (R S : Fin 3 → ZMod 2) (C D : Fin 2 → ZMod 2), (∀ r, R r*S r=0) ∧
      ∀ r s i j, binaryTriangle (r,i) (s,j)=(R r*S s+S r*R s)*(C i*D j+D i*C j) := by
  decide +kernel

#print axioms binary_triangle_rank
#print axioms binary_triangle_overlaps
end HollowGrid
