import Signed19ColdPrime3Data

namespace Signed39.Contraction
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice19x3x36 : divisorGridSlice 3 19 64 qInputs_3_19 keep_3_19 36 := by decide +kernel
theorem slice19x3x37 : divisorGridSlice 3 19 64 qInputs_3_19 keep_3_19 37 := by decide +kernel
end Signed39.Contraction
