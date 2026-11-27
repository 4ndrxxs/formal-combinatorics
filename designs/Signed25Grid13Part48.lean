import Signed25Grid13Data

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid13x25Case48: divisorGridSlice 13 25 177 qInputs_13_25 keep_13_25 48 := by decide +kernel

theorem grid13x25Case49: divisorGridSlice 13 25 177 qInputs_13_25 keep_13_25 49 := by decide +kernel

end Signed39.Contraction
