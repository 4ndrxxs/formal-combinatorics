module
public import Quantum.FractionalTwo.Data

@[expose] public section
namespace FractionalTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem checkedPart544 : Interval checked 544 548 :=
  interval_fin 544 548 (by decide +kernel)
private theorem checkedPart548 : Interval checked 548 572 :=
  interval_fin 548 572 (by decide +kernel)
private theorem checkedPart572 : Interval checked 572 576 :=
  interval_fin 572 576 (by decide +kernel)
private theorem checkedPart576 : Interval checked 576 581 :=
  interval_fin 576 581 (by decide +kernel)
private theorem checkedPart581 : Interval checked 581 586 :=
  interval_fin 581 586 (by decide +kernel)
private theorem checkedPart586 : Interval checked 586 605 :=
  interval_fin 586 605 (by decide +kernel)
private theorem checkedPart605 : Interval checked 605 611 :=
  interval_fin 605 611 (by decide +kernel)
private theorem checkedPart611 : Interval checked 611 625 :=
  interval_fin 611 625 (by decide +kernel)
private theorem checkedPart625 : Interval checked 625 641 :=
  interval_fin 625 641 (by decide +kernel)
theorem checked05 : Interval checked 544 641 := (interval_join (interval_join (interval_join checkedPart544 checkedPart548) (interval_join checkedPart572 checkedPart576)) (interval_join (interval_join checkedPart581 checkedPart586) (interval_join checkedPart605 (interval_join checkedPart611 checkedPart625))))
end FractionalTwo
