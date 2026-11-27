import Signed25Grid7Data

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid7x25Case48: divisorGridSlice 7 25 130 qInputs_7_25 keep_7_25 48 := by decide +kernel

theorem grid7x25Case49: divisorGridSlice 7 25 130 qInputs_7_25 keep_7_25 49 := by decide +kernel

end Signed39.Contraction
