import Signed25Grid19Data

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid19x25Case48: divisorGridSlice 19 25 214 qInputs_19_25 keep_19_25 48 := by decide +kernel

theorem grid19x25Case49: divisorGridSlice 19 25 214 qInputs_19_25 keep_19_25 49 := by decide +kernel

end Signed39.Contraction
