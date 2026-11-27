module
public import Quantum.FractionalTwo.Data

@[expose] public section
namespace FractionalTwo
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem checkedPart166 : Interval checked 166 172 :=
  interval_fin 166 172 (by decide +kernel)
private theorem checkedPart172 : Interval checked 172 181 :=
  interval_fin 172 181 (by decide +kernel)
private theorem checkedPart181 : Interval checked 181 191 :=
  interval_fin 181 191 (by decide +kernel)
private theorem checkedPart191 : Interval checked 191 197 :=
  interval_fin 191 197 (by decide +kernel)
private theorem checkedPart197 : Interval checked 197 202 :=
  interval_fin 197 202 (by decide +kernel)
private theorem checkedPart202 : Interval checked 202 207 :=
  interval_fin 202 207 (by decide +kernel)
private theorem checkedPart207 : Interval checked 207 211 :=
  interval_fin 207 211 (by decide +kernel)
private theorem checkedPart211 : Interval checked 211 215 :=
  interval_fin 211 215 (by decide +kernel)
private theorem checkedPart215 : Interval checked 215 218 :=
  interval_fin 215 218 (by decide +kernel)
private theorem checkedPart218 : Interval checked 218 226 :=
  interval_fin 218 226 (by decide +kernel)
private theorem checkedPart226 : Interval checked 226 232 :=
  interval_fin 226 232 (by decide +kernel)
private theorem checkedPart232 : Interval checked 232 245 :=
  interval_fin 232 245 (by decide +kernel)
private theorem checkedPart245 : Interval checked 245 252 :=
  interval_fin 245 252 (by decide +kernel)
private theorem checkedPart252 : Interval checked 252 257 :=
  interval_fin 252 257 (by decide +kernel)
private theorem checkedPart257 : Interval checked 257 260 :=
  interval_fin 257 260 (by decide +kernel)
private theorem checkedPart260 : Interval checked 260 265 :=
  interval_fin 260 265 (by decide +kernel)
theorem checked02 : Interval checked 166 265 := (interval_join (interval_join (interval_join (interval_join checkedPart166 checkedPart172) (interval_join checkedPart181 checkedPart191)) (interval_join (interval_join checkedPart197 checkedPart202) (interval_join checkedPart207 checkedPart211))) (interval_join (interval_join (interval_join checkedPart215 checkedPart218) (interval_join checkedPart226 checkedPart232)) (interval_join (interval_join checkedPart245 checkedPart252) (interval_join checkedPart257 checkedPart260))))
end FractionalTwo
