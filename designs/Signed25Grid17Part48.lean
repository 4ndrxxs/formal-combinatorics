import Signed25Grid17Data

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid17x25Case48: divisorGridSlice 17 25 202 qInputs_17_25 keep_17_25 48 := by decide +kernel

theorem grid17x25Case49: divisorGridSlice 17 25 202 qInputs_17_25 keep_17_25 49 := by decide +kernel

end Signed39.Contraction
