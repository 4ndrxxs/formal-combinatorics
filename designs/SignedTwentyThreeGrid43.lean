import SignedTwentyThreeGrid43Part0
import SignedTwentyThreeGrid43Part8
import SignedTwentyThreeGrid43Part16
import SignedTwentyThreeGrid43Part24
import SignedTwentyThreeGrid43Part32
import SignedTwentyThreeGrid43Part40

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_43_23 : divisorGrid 43 23 296 qInputs_43_23 keep_43_23 := by
  intro d
  fin_cases d
  · exact grid43Case0
  · exact grid43Case1
  · exact grid43Case2
  · exact grid43Case3
  · exact grid43Case4
  · exact grid43Case5
  · exact grid43Case6
  · exact grid43Case7
  · exact grid43Case8
  · exact grid43Case9
  · exact grid43Case10
  · exact grid43Case11
  · exact grid43Case12
  · exact grid43Case13
  · exact grid43Case14
  · exact grid43Case15
  · exact grid43Case16
  · exact grid43Case17
  · exact grid43Case18
  · exact grid43Case19
  · exact grid43Case20
  · exact grid43Case21
  · exact grid43Case22
  · exact grid43Case23
  · exact grid43Case24
  · exact grid43Case25
  · exact grid43Case26
  · exact grid43Case27
  · exact grid43Case28
  · exact grid43Case29
  · exact grid43Case30
  · exact grid43Case31
  · exact grid43Case32
  · exact grid43Case33
  · exact grid43Case34
  · exact grid43Case35
  · exact grid43Case36
  · exact grid43Case37
  · exact grid43Case38
  · exact grid43Case39
  · exact grid43Case40
  · exact grid43Case41
  · exact grid43Case42
  · exact grid43Case43
  · exact grid43Case44
  · exact grid43Case45

end Signed39.Contraction
