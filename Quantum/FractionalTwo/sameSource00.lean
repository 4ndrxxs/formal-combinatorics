module
public import Quantum.FractionalTwo.Data

@[expose] public section
namespace FractionalTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem sameSourcePart0 : Interval sameSource 0 48 :=
  interval_fin 0 48 (by decide +kernel)
private theorem sameSourcePart48 : Interval sameSource 48 96 :=
  interval_fin 48 96 (by decide +kernel)
private theorem sameSourcePart96 : Interval sameSource 96 144 :=
  interval_fin 96 144 (by decide +kernel)
private theorem sameSourcePart144 : Interval sameSource 144 192 :=
  interval_fin 144 192 (by decide +kernel)
private theorem sameSourcePart192 : Interval sameSource 192 240 :=
  interval_fin 192 240 (by decide +kernel)
private theorem sameSourcePart240 : Interval sameSource 240 288 :=
  interval_fin 240 288 (by decide +kernel)
private theorem sameSourcePart288 : Interval sameSource 288 336 :=
  interval_fin 288 336 (by decide +kernel)
private theorem sameSourcePart336 : Interval sameSource 336 384 :=
  interval_fin 336 384 (by decide +kernel)
private theorem sameSourcePart384 : Interval sameSource 384 432 :=
  interval_fin 384 432 (by decide +kernel)
private theorem sameSourcePart432 : Interval sameSource 432 480 :=
  interval_fin 432 480 (by decide +kernel)
private theorem sameSourcePart480 : Interval sameSource 480 528 :=
  interval_fin 480 528 (by decide +kernel)
private theorem sameSourcePart528 : Interval sameSource 528 576 :=
  interval_fin 528 576 (by decide +kernel)
private theorem sameSourcePart576 : Interval sameSource 576 624 :=
  interval_fin 576 624 (by decide +kernel)
private theorem sameSourcePart624 : Interval sameSource 624 672 :=
  interval_fin 624 672 (by decide +kernel)
private theorem sameSourcePart672 : Interval sameSource 672 720 :=
  interval_fin 672 720 (by decide +kernel)
private theorem sameSourcePart720 : Interval sameSource 720 768 :=
  interval_fin 720 768 (by decide +kernel)
theorem sameSource00 : Interval sameSource 0 768 := (interval_join (interval_join (interval_join (interval_join sameSourcePart0 sameSourcePart48) (interval_join sameSourcePart96 sameSourcePart144)) (interval_join (interval_join sameSourcePart192 sameSourcePart240) (interval_join sameSourcePart288 sameSourcePart336))) (interval_join (interval_join (interval_join sameSourcePart384 sameSourcePart432) (interval_join sameSourcePart480 sameSourcePart528)) (interval_join (interval_join sameSourcePart576 sameSourcePart624) (interval_join sameSourcePart672 sameSourcePart720))))
end FractionalTwo
