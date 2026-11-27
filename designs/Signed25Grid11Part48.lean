import Signed25Grid11Data

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid11x25Case48: divisorGridSlice 11 25 163 qInputs_11_25 keep_11_25 48 := by decide +kernel

theorem grid11x25Case49: divisorGridSlice 11 25 163 qInputs_11_25 keep_11_25 49 := by decide +kernel

end Signed39.Contraction
