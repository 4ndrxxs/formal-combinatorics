import PermanentTwelveShapes

/-! Each single deletion of a canonical thirteen-cell board is identified
with a twelve-cell representative by two explicit permutations. -/

namespace PermanentFive
open Equiv Finset
private def layoutPerm : Fin 12 → Perm Idx :=
  ![Equiv.refl Idx, (Equiv.swap 2 3), (Equiv.swap 2 4), (Equiv.swap 0 1), (Equiv.swap 1 2), (Equiv.swap 1 3), (Equiv.swap 1 4), ((Equiv.swap 1 2).trans (Equiv.swap 1 3)), ((Equiv.swap 1 2).trans (Equiv.swap 1 4)), (Equiv.swap 0 2), ((Equiv.swap 0 2).trans (Equiv.swap 0 3)), ((Equiv.swap 0 2).trans (Equiv.swap 0 4))]

private def layout : Fin 4 → Idx → Idx → Fin 9 × Fin 12 × Fin 12 :=
  ![
    ![![(0,0,0), (0,0,0), (0,0,0), (0,0,1), (0,0,2)], ![(1,0,0), (1,0,3), (2,0,0), (2,0,1), (2,0,2)], ![(1,4,0), (1,4,3), (2,4,0), (2,4,1), (2,4,2)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)]],
    ![![(0,0,0), (1,0,0), (1,0,4), (1,0,5), (1,0,6)], ![(0,0,0), (1,3,0), (1,3,4), (1,3,5), (1,3,6)], ![(3,0,0), (4,0,0), (4,0,4), (4,0,5), (4,0,6)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)]],
    ![![(0,0,0), (1,0,3), (2,0,4), (2,0,7), (2,0,8)], ![(1,3,0), (0,0,0), (2,3,9), (2,3,10), (2,3,11)], ![(4,4,0), (4,9,3), (5,0,0), (5,0,1), (5,0,2)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(0,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)]],
    ![![(6,0,0), (7,0,0), (7,0,4), (7,0,5), (7,0,6)], ![(6,3,0), (7,3,0), (7,3,4), (7,3,5), (7,3,6)], ![(8,0,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(8,1,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)], ![(8,2,0), (0,0,0), (0,0,0), (0,0,0), (0,0,0)]]]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 24000000 in
private theorem checked_layout : ∀ t, ∀ x ∈ thirteenShape t, ∀ j ∈ (thirteenShape t).erase x,
    ((layoutPerm (layout t x.1 x.2).2.1).prodCongr
      (layoutPerm (layout t x.1 x.2).2.2)) j ∈ twelveShape (layout t x.1 x.2).1 := by
  intro t
  fin_cases t <;> decide +kernel

theorem twelve_deletion (t : Fin 4) (x : Cell) (hx : x ∈ thirteenShape t) :
    ∃ (i : Fin 9) (r c : Perm Idx),
      ∀ j ∈ (thirteenShape t).erase x, (r.prodCongr c) j ∈ twelveShape i :=
  ⟨_,_,_,checked_layout t x hx⟩

#print axioms twelve_deletion
end PermanentFive
