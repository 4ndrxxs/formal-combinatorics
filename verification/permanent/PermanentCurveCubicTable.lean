import PermanentCurvePlane
noncomputable section
open PermanentFive
namespace PermanentCurve
set_option maxRecDepth 18000 in
set_option maxHeartbeats 120000000 in
theorem cubic_table (a b : Fin 4) (i j : Idx) :
    actual (a.val : ℤ) (b.val : ℤ) i j = block (a.val : ℤ) (b.val : ℤ) i j := by
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> decide +kernel

end PermanentCurve
