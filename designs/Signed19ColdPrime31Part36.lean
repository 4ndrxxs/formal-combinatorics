import Signed19ColdPrime31Data

namespace Signed39.Contraction
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem slice19x31x36 : divisorGridSlice 31 19 206 qInputs_31_19 keep_31_19 36 := by decide +kernel
theorem slice19x31x37 : divisorGridSlice 31 19 206 qInputs_31_19 keep_31_19 37 := by decide +kernel
end Signed39.Contraction
