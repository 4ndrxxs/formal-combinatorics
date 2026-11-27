module
public import Quantum.FractionalTwo.Data

@[expose] public section
namespace FractionalTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem checkedPart464 : Interval checked 464 468 :=
  interval_fin 464 468 (by decide +kernel)
private theorem checkedPart468 : Interval checked 468 473 :=
  interval_fin 468 473 (by decide +kernel)
private theorem checkedPart473 : Interval checked 473 478 :=
  interval_fin 473 478 (by decide +kernel)
private theorem checkedPart478 : Interval checked 478 485 :=
  interval_fin 478 485 (by decide +kernel)
private theorem checkedPart485 : Interval checked 485 492 :=
  interval_fin 485 492 (by decide +kernel)
private theorem checkedPart492 : Interval checked 492 498 :=
  interval_fin 492 498 (by decide +kernel)
private theorem checkedPart498 : Interval checked 498 503 :=
  interval_fin 498 503 (by decide +kernel)
private theorem checkedPart503 : Interval checked 503 507 :=
  interval_fin 503 507 (by decide +kernel)
private theorem checkedPart507 : Interval checked 507 513 :=
  interval_fin 507 513 (by decide +kernel)
private theorem checkedPart513 : Interval checked 513 517 :=
  interval_fin 513 517 (by decide +kernel)
private theorem checkedPart517 : Interval checked 517 523 :=
  interval_fin 517 523 (by decide +kernel)
private theorem checkedPart523 : Interval checked 523 527 :=
  interval_fin 523 527 (by decide +kernel)
private theorem checkedPart527 : Interval checked 527 531 :=
  interval_fin 527 531 (by decide +kernel)
private theorem checkedPart531 : Interval checked 531 536 :=
  interval_fin 531 536 (by decide +kernel)
private theorem checkedPart536 : Interval checked 536 540 :=
  interval_fin 536 540 (by decide +kernel)
private theorem checkedPart540 : Interval checked 540 544 :=
  interval_fin 540 544 (by decide +kernel)
theorem checked04 : Interval checked 464 544 := (interval_join (interval_join (interval_join (interval_join checkedPart464 checkedPart468) (interval_join checkedPart473 checkedPart478)) (interval_join (interval_join checkedPart485 checkedPart492) (interval_join checkedPart498 checkedPart503))) (interval_join (interval_join (interval_join checkedPart507 checkedPart513) (interval_join checkedPart517 checkedPart523)) (interval_join (interval_join checkedPart527 checkedPart531) (interval_join checkedPart536 checkedPart540))))
end FractionalTwo
