module
public import Quantum.FractionalTwo.Data

@[expose] public section
namespace FractionalTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem checkedPart0 : Interval checked 0 23 :=
  interval_fin 0 23 (by decide +kernel)
private theorem checkedPart23 : Interval checked 23 26 :=
  interval_fin 23 26 (by decide +kernel)
private theorem checkedPart26 : Interval checked 26 29 :=
  interval_fin 26 29 (by decide +kernel)
private theorem checkedPart29 : Interval checked 29 32 :=
  interval_fin 29 32 (by decide +kernel)
private theorem checkedPart32 : Interval checked 32 36 :=
  interval_fin 32 36 (by decide +kernel)
private theorem checkedPart36 : Interval checked 36 40 :=
  interval_fin 36 40 (by decide +kernel)
private theorem checkedPart40 : Interval checked 40 43 :=
  interval_fin 40 43 (by decide +kernel)
private theorem checkedPart43 : Interval checked 43 47 :=
  interval_fin 43 47 (by decide +kernel)
private theorem checkedPart47 : Interval checked 47 51 :=
  interval_fin 47 51 (by decide +kernel)
private theorem checkedPart51 : Interval checked 51 54 :=
  interval_fin 51 54 (by decide +kernel)
private theorem checkedPart54 : Interval checked 54 57 :=
  interval_fin 54 57 (by decide +kernel)
private theorem checkedPart57 : Interval checked 57 60 :=
  interval_fin 57 60 (by decide +kernel)
private theorem checkedPart60 : Interval checked 60 64 :=
  interval_fin 60 64 (by decide +kernel)
private theorem checkedPart64 : Interval checked 64 67 :=
  interval_fin 64 67 (by decide +kernel)
private theorem checkedPart67 : Interval checked 67 70 :=
  interval_fin 67 70 (by decide +kernel)
private theorem checkedPart70 : Interval checked 70 73 :=
  interval_fin 70 73 (by decide +kernel)
theorem checked00 : Interval checked 0 73 := (interval_join (interval_join (interval_join (interval_join checkedPart0 checkedPart23) (interval_join checkedPart26 checkedPart29)) (interval_join (interval_join checkedPart32 checkedPart36) (interval_join checkedPart40 checkedPart43))) (interval_join (interval_join (interval_join checkedPart47 checkedPart51) (interval_join checkedPart54 checkedPart57)) (interval_join (interval_join checkedPart60 checkedPart64) (interval_join checkedPart67 checkedPart70))))
end FractionalTwo
