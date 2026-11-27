import PermanentCurveArithmetic
noncomputable section
namespace PermanentCurve
set_option maxRecDepth 18000 in
set_option maxHeartbeats 120000000 in
theorem determinant_table (a b : Fin 16) :
    (block (a.val : ℤ) (b.val : ℤ)).det = rhs (a.val : ℤ) (b.val : ℤ) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

end PermanentCurve
