import PermanentArrowTable
noncomputable section
open PermanentFive PermanentBorder
namespace PermanentArrow
set_option maxRecDepth 100000
set_option maxHeartbeats 150000000
theorem small_3 : ∀ (e f : CellOf (Fin 3)), secondAt (point ℤ (0:Fin 3)) e f=entry (0:Fin 3) e f := by
  decide +kernel
end PermanentArrow
