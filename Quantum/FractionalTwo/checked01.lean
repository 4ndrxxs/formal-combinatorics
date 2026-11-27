module
public import Quantum.FractionalTwo.Data

@[expose] public section
namespace FractionalTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem checkedPart73 : Interval checked 73 76 :=
  interval_fin 73 76 (by decide +kernel)
private theorem checkedPart76 : Interval checked 76 79 :=
  interval_fin 76 79 (by decide +kernel)
private theorem checkedPart79 : Interval checked 79 84 :=
  interval_fin 79 84 (by decide +kernel)
private theorem checkedPart84 : Interval checked 84 87 :=
  interval_fin 84 87 (by decide +kernel)
private theorem checkedPart87 : Interval checked 87 90 :=
  interval_fin 87 90 (by decide +kernel)
private theorem checkedPart90 : Interval checked 90 96 :=
  interval_fin 90 96 (by decide +kernel)
private theorem checkedPart96 : Interval checked 96 101 :=
  interval_fin 96 101 (by decide +kernel)
private theorem checkedPart101 : Interval checked 101 107 :=
  interval_fin 101 107 (by decide +kernel)
private theorem checkedPart107 : Interval checked 107 116 :=
  interval_fin 107 116 (by decide +kernel)
private theorem checkedPart116 : Interval checked 116 125 :=
  interval_fin 116 125 (by decide +kernel)
private theorem checkedPart125 : Interval checked 125 132 :=
  interval_fin 125 132 (by decide +kernel)
private theorem checkedPart132 : Interval checked 132 138 :=
  interval_fin 132 138 (by decide +kernel)
private theorem checkedPart138 : Interval checked 138 145 :=
  interval_fin 138 145 (by decide +kernel)
private theorem checkedPart145 : Interval checked 145 152 :=
  interval_fin 145 152 (by decide +kernel)
private theorem checkedPart152 : Interval checked 152 159 :=
  interval_fin 152 159 (by decide +kernel)
private theorem checkedPart159 : Interval checked 159 166 :=
  interval_fin 159 166 (by decide +kernel)
theorem checked01 : Interval checked 73 166 := (interval_join (interval_join (interval_join (interval_join checkedPart73 checkedPart76) (interval_join checkedPart79 checkedPart84)) (interval_join (interval_join checkedPart87 checkedPart90) (interval_join checkedPart96 checkedPart101))) (interval_join (interval_join (interval_join checkedPart107 checkedPart116) (interval_join checkedPart125 checkedPart132)) (interval_join (interval_join checkedPart138 checkedPart145) (interval_join checkedPart152 checkedPart159))))
end FractionalTwo
