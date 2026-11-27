module
public import Quantum.FractionalTwo.Data

@[expose] public section
namespace FractionalTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem checkedPart265 : Interval checked 265 269 :=
  interval_fin 265 269 (by decide +kernel)
private theorem checkedPart269 : Interval checked 269 279 :=
  interval_fin 269 279 (by decide +kernel)
private theorem checkedPart279 : Interval checked 279 285 :=
  interval_fin 279 285 (by decide +kernel)
private theorem checkedPart285 : Interval checked 285 288 :=
  interval_fin 285 288 (by decide +kernel)
private theorem checkedPart288 : Interval checked 288 292 :=
  interval_fin 288 292 (by decide +kernel)
private theorem checkedPart292 : Interval checked 292 299 :=
  interval_fin 292 299 (by decide +kernel)
private theorem checkedPart299 : Interval checked 299 303 :=
  interval_fin 299 303 (by decide +kernel)
private theorem checkedPart303 : Interval checked 303 359 :=
  interval_fin 303 359 (by decide +kernel)
private theorem checkedPart359 : Interval checked 359 401 :=
  interval_fin 359 401 (by decide +kernel)
private theorem checkedPart401 : Interval checked 401 421 :=
  interval_fin 401 421 (by decide +kernel)
private theorem checkedPart421 : Interval checked 421 438 :=
  interval_fin 421 438 (by decide +kernel)
private theorem checkedPart438 : Interval checked 438 443 :=
  interval_fin 438 443 (by decide +kernel)
private theorem checkedPart443 : Interval checked 443 449 :=
  interval_fin 443 449 (by decide +kernel)
private theorem checkedPart449 : Interval checked 449 456 :=
  interval_fin 449 456 (by decide +kernel)
private theorem checkedPart456 : Interval checked 456 460 :=
  interval_fin 456 460 (by decide +kernel)
private theorem checkedPart460 : Interval checked 460 464 :=
  interval_fin 460 464 (by decide +kernel)
theorem checked03 : Interval checked 265 464 := (interval_join (interval_join (interval_join (interval_join checkedPart265 checkedPart269) (interval_join checkedPart279 checkedPart285)) (interval_join (interval_join checkedPart288 checkedPart292) (interval_join checkedPart299 checkedPart303))) (interval_join (interval_join (interval_join checkedPart359 checkedPart401) (interval_join checkedPart421 checkedPart438)) (interval_join (interval_join checkedPart443 checkedPart449) (interval_join checkedPart456 checkedPart460))))
end FractionalTwo
