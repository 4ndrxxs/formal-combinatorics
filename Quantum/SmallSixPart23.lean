module
public import Quantum.SmallSixNumbers
public import Quantum.Biquadratic
public import Quantum.SmallSixRational29
/-! Explicit order-six quantum Latin squares, checked over the complex numbers. -/
@[expose] public section
namespace SmallSix
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet23 : Array SmallSixNumbers.Quad := #[((-1, 0), (0, 0)), ((0, -1), (0, 0)), ((0, 0), (0, 0)), ((0, 1), (0, 0)), ((1, 0), (0, 0)), ((2, 0), (0, 0))]
private def words23 : Array ℕ := #[21254, 18664, 34214, 18674, 18734, 19094, 18932, 18485, 18868, 18640, 18428, 18845, 18436,
    18712, 18616, 18688, 36806, 18676, 5702, 18892, 18460, 18652, 19166]
private def slots23 : Array (Fin 23) := #[0, 1, 2, 3, 4, 5,
    2, 0, 6, 7, 8, 9,
    10, 2, 0, 11, 12, 13,
    14, 5, 15, 16, 17, 18,
    19, 4, 20, 18, 16, 21,
    7, 3, 11, 22, 18, 16]
private def pivots23 : Array (Fin 6) := #[4, 0, 5, 1, 2, 3, 1, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 4, 0, 4, 0, 0, 0, 2]

theorem card23 : Realized 6 23 := by
  apply (SmallSixNumbers.model 2 (by exact (show Nat.Prime 2 by decide).not_isSquare)).certify
    (fun i x => alphabet23[(words23[i.val]! / 6 ^ x.val) % 6]!)
    (fun p => slots23[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (SmallSixNumbers.model 2 (by exact (show Nat.Prime 2 by decide).not_isSquare)).distinct_of_pivots (fun i => pivots23[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card23


private def alphabet24 : Array IQ := #[(-2, 0), (-1, -1), (-1, 0), (-1, 1), (1, -1), (1, 0), (1, 1),
    (2, 0)]
private def words24 : Array ℕ := #[187245, 173229, 111567, 117775, 36127, 62175, 75117, 88749, 150991, 143887, 226079, 199903, 48735,
    49567, 234111, 257471, 213087, 212895, 27775, 5055, 106191, 123151, 155855, 139023]
private def slots24 : Array (Fin 24) := #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 3, 2,
    16, 17, 18, 19, 9, 8,
    20, 21, 5, 4, 15, 14,
    22, 23, 11, 10, 19, 18]
private def pivots24 : Array (Fin 6) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem card24 : Realized 6 24 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet24[(words24[i.val]! / 8 ^ x.val) % 8]!)
    (fun p => slots24[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots24[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card24


private def alphabet25 : Array SmallSixNumbers.Quad := #[((-2, 0), (0, 0)), ((-1, 0), (0, 0)), ((0, -2), (0, 0)), ((0, -1), (0, 0)), ((0, 0), (0, 0)), ((0, 1), (0, 0)), ((0, 2), (0, 0)),
    ((1, 0), (0, 0)), ((2, 0), (0, 0)), ((4, 0), (0, 0))]
private def words25 : Array ℕ := #[474444, 444447, 744444, 444474, 444744, 447444, 445574, 443547, 445408, 444388, 443394, 445349, 442417,
    444677, 444217, 444508, 774444, 444477, 174444, 446477, 443488, 444417, 443549, 445347, 447744]
private def slots25 : Array (Fin 25) := #[0, 1, 2, 3, 4, 5,
    2, 0, 6, 7, 8, 9,
    10, 2, 0, 11, 12, 13,
    14, 5, 15, 16, 17, 18,
    19, 4, 20, 18, 16, 21,
    22, 3, 23, 24, 18, 16]
private def pivots25 : Array (Fin 6) := #[4, 0, 5, 1, 2, 3, 1, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0, 2]

theorem card25 : Realized 6 25 := by
  apply (SmallSixNumbers.model 2 (by exact (show Nat.Prime 2 by decide).not_isSquare)).certify
    (fun i x => alphabet25[(words25[i.val]! / 10 ^ x.val) % 10]!)
    (fun p => slots25[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (SmallSixNumbers.model 2 (by exact (show Nat.Prime 2 by decide).not_isSquare)).distinct_of_pivots (fun i => pivots25[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card25


private def alphabet26 : Array ℤ :=
  #[-36, -20, -15, -12, -9, -5,
    -3, 0, 1, 3, 4, 5,
    9, 12, 15, 16, 20, 36,
    48]
private def words26 : Array ℕ :=
  #[18425941, 20771719, 18302479, 18295981, 18295588, 18295738, 18295262, 18288818, 18374515, 18258352, 18295604, 18295679, 18284068,
    18338218, 18352777, 18271021, 18246020, 18341003, 18289844, 18316919, 18295639, 18295621, 18267259, 18328403, 18296705, 18316235]
private def labels26 : Array (Fin 26) :=
  #[0, 1, 2, 3, 4, 5,
    1, 0, 6, 7, 8, 9,
    10, 11, 0, 1, 12, 13,
    14, 15, 1, 0, 16, 17,
    18, 19, 20, 21, 0, 1,
    22, 23, 24, 25, 1, 0]
private def pivots26 : Array (Fin 6) :=
  #[4, 5, 3, 2, 0, 0, 0, 1, 0, 0, 0, 0, 2,
    2, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 1]

theorem card26 : Realized 6 26 := by
  apply integerModel.certify
    (fun i x => alphabet26[(words26[i.val]! / 19 ^ x.val) % 19]!)
    (fun p => labels26[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots26[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card26


private def alphabet27 : Array IQ := #[(-2, 0), (-1, -1), (-1, 1), (1, -1), (1, 0), (1, 1), (2, 0)]
private def words27 : Array ℕ := #[78432, 36798, 22098, 34943, 30582, 108149, 20040, 106329, 50175, 114666, 41117, 17891, 38856,
    33417, 104271, 24065, 101975, 47634, 29112, 109129, 35433, 41950, 18822, 112902, 102612, 45723,
    25339]
private def slots27 : Array (Fin 27) := #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17,
    18, 19, 20, 14, 12, 13,
    21, 22, 23, 2, 0, 1,
    24, 25, 26, 8, 6, 7]
private def pivots27 : Array (Fin 6) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0]

theorem card27 : Realized 6 27 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet27[(words27[i.val]! / 7 ^ x.val) % 7]!)
    (fun p => slots27[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots27[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card27


private def alphabet28 : Array ℤ :=
  #[-36, -20, -15, -12, -9, -5,
    -3, 0, 1, 3, 4, 5,
    9, 12, 15, 16, 20, 36,
    48]
private def words28 : Array ℕ :=
  #[18425941, 20771719, 18302479, 18295981, 18295588, 18295738, 18295262, 18288818, 18374515, 18258352, 18295604, 18295679, 25984559,
    16210484, 18284068, 18338218, 18352777, 18271021, 18246020, 18341003, 18289844, 18316919, 18295639, 18295621, 18267259, 18328403,
    18296705, 18316235]
private def labels28 : Array (Fin 28) :=
  #[0, 1, 2, 3, 4, 5,
    1, 0, 6, 7, 8, 9,
    10, 11, 12, 13, 14, 15,
    16, 17, 13, 12, 18, 19,
    20, 21, 22, 23, 12, 13,
    24, 25, 26, 27, 13, 12]
private def pivots28 : Array (Fin 6) :=
  #[4, 5, 3, 2, 0, 0, 0, 1, 0, 0, 0, 0, 4,
    4, 2, 2, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0,
    0, 1]

theorem card28 : Realized 6 28 := by
  apply integerModel.certify
    (fun i x => alphabet28[(words28[i.val]! / 19 ^ x.val) % 19]!)
    (fun p => labels28[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots28[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card28

theorem card29 : Realized 6 29 := SmallSixRational29.realized

end SmallSix
