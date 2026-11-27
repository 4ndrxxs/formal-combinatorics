import Signed25Grid31Data

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid31x25Case48: divisorGridSlice 31 25 273 qInputs_31_25 keep_31_25 48 := by decide +kernel

theorem grid31x25Case49: divisorGridSlice 31 25 273 qInputs_31_25 keep_31_25 49 := by decide +kernel

end Signed39.Contraction
