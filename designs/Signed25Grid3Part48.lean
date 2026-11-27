import Signed25Grid3Data

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid3x25Case48: divisorGridSlice 3 25 85 qInputs_3_25 keep_3_25 48 := by decide +kernel

theorem grid3x25Case49: divisorGridSlice 3 25 85 qInputs_3_25 keep_3_25 49 := by decide +kernel

end Signed39.Contraction
