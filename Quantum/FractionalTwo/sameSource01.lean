module
public import Quantum.FractionalTwo.Data

@[expose] public section
namespace FractionalTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem sameSourcePart768 : Interval sameSource 768 814 :=
  interval_fin 768 814 (by decide +kernel)
theorem sameSource01 : Interval sameSource 768 814 := sameSourcePart768
end FractionalTwo
