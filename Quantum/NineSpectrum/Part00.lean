module
public import Quantum.Pivots
/-! Explicit order-nine quantum Latin squares with kernel-checked coefficient arithmetic. -/
@[expose] public section
namespace NineSpectrum
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet9 : Array ℤ :=
  #[0, 1]
private def words9 : Array ℕ :=
  #[32, 64, 128, 256, 16, 4, 2, 1, 8]
private def labels9 : Array (Fin 9) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    2, 3, 0, 1, 6, 8, 7, 4, 5,
    3, 0, 1, 2, 8, 7, 4, 5, 6,
    1, 2, 3, 0, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 1, 0, 3, 2,
    5, 8, 7, 4, 0, 6, 3, 2, 1,
    6, 7, 4, 8, 1, 2, 5, 0, 3,
    7, 4, 5, 6, 2, 3, 1, 8, 0,
    8, 5, 6, 7, 3, 0, 2, 1, 4]
private def pivots9 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3]

theorem card9 : Realized 9 9 := by
  apply integerModel.certify
    (fun i x => alphabet9[(words9[i.val]! / 2 ^ x.val) % 2]!)
    (fun p => labels9[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots9[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card9

end NineSpectrum
