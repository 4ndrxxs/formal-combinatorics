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

private def alphabet15 : Array ℤ :=
  #[-8, -7, -4, 0, 1, 3,
    4, 7, 8, 15, 24]
private def words15 : Array ℕ :=
  #[692519, 619919, 540789, 531479, 528813, 488271, 532799, 531469, 633999, 531589, 502263, 560753, 370659,
    516829, 853933]
private def labels15 : Array (Fin 15) :=
  #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 9, 10, 0,
    11, 6, 12, 13, 14, 3,
    13, 3, 14, 11, 12, 6,
    9, 0, 10, 6, 8, 7,
    3, 5, 4, 0, 2, 1]
private def pivots15 : Array (Fin 6) :=
  #[5, 2, 0, 1, 0, 2, 3, 0, 1, 2, 1, 0, 2,
    0, 2]

theorem card15 : Realized 6 15 := by
  apply integerModel.certify
    (fun i x => alphabet15[(words15[i.val]! / 11 ^ x.val) % 11]!)
    (fun p => labels15[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots15[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card15


private def alphabet16 : Array ℤ :=
  #[-24, -12, -7, -5, 0, 1,
    5, 7, 12, 24]
private def words16 : Array ℕ :=
  #[447494, 464844, 944447, 414644, 244449, 440474, 454444, 844446, 444544, 344448, 544444, 444454, 445444,
    444445, 474944, 404744]
private def labels16 : Array (Fin 16) :=
  #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 0, 5, 9,
    10, 11, 12, 13, 14, 15,
    8, 9, 6, 5, 0, 7,
    13, 12, 11, 10, 15, 14,
    5, 3, 4, 1, 2, 0]
private def pivots16 : Array (Fin 6) :=
  #[1, 2, 0, 2, 0, 1, 4, 0, 2, 0, 5, 1, 3,
    0, 2, 2]

theorem card16 : Realized 6 16 := by
  apply integerModel.certify
    (fun i x => alphabet16[(words16[i.val]! / 10 ^ x.val) % 10]!)
    (fun p => labels16[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots16[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card16


private def alphabet17 : Array ℤ :=
  #[-63, -8, -7, -4, 0, 1,
    3, 4, 7, 8, 15, 16,
    24, 63]
private def words17 : Array ℕ :=
  #[2854604, 2548256, 2338736, 2316794, 2311300, 2202708, 2319524, 2316781, 2624164, 2316976, 2240060, 2393615, 2308632,
    6083312, 2278366, 166856, 2333314]
private def labels17 : Array (Fin 17) :=
  #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 9, 10, 0,
    11, 12, 13, 14, 15, 16,
    14, 16, 15, 11, 13, 12,
    9, 0, 10, 6, 8, 7,
    3, 5, 4, 0, 2, 1]
private def pivots17 : Array (Fin 6) :=
  #[5, 2, 0, 1, 0, 2, 3, 0, 1, 2, 1, 0, 1,
    2, 0, 2, 1]

theorem card17 : Realized 6 17 := by
  apply integerModel.certify
    (fun i x => alphabet17[(words17[i.val]! / 14 ^ x.val) % 14]!)
    (fun p => labels17[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots17[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card17


private def alphabet18 : Array ℤ :=
  #[-24, -12, -7, -5, -3, 0,
    1, 3, 4, 5, 7, 12,
    24]
private def words18 : Array ℕ :=
  #[2022246, 2126428, 4610226, 1897602, 897298, 2000250, 2039731, 4238932, 2011339, 2009012, 2017787, 1268590, 2382463,
    2011183, 2013367, 2011171, 2155158, 1869210]
private def labels18 : Array (Fin 18) :=
  #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17,
    8, 11, 6, 10, 9, 7,
    15, 14, 13, 12, 17, 16,
    5, 3, 4, 1, 2, 0]
private def pivots18 : Array (Fin 6) :=
  #[1, 2, 0, 2, 0, 1, 4, 0, 2, 1, 1, 0, 5,
    1, 3, 0, 2, 2]

theorem card18 : Realized 6 18 := by
  apply integerModel.certify
    (fun i x => alphabet18[(words18[i.val]! / 13 ^ x.val) % 13]!)
    (fun p => labels18[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots18[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card18


private def alphabet19 : Array SmallSixNumbers.Quad := #[((-2, 0), (0, 0)), ((0, -1), (0, -1)), ((0, -1), (0, 1)), ((0, 0), (-2, 0)), ((0, 0), (2, 0)), ((0, 1), (0, -1)), ((0, 1), (0, 1)),
    ((2, 0), (0, 0))]
private def words19 : Array ℕ := #[262143, 131327, 11039, 89159, 169351, 123431, 98623, 152607, 205639, 60039, 7399, 166047, 82271,
    145159, 198247, 14399, 45479, 17983, 116935]
private def slots19 : Array (Fin 19) := #[0, 1, 2, 3, 4, 5,
    6, 0, 7, 8, 9, 10,
    10, 5, 0, 11, 12, 13,
    9, 4, 14, 0, 15, 12,
    8, 3, 16, 17, 0, 11,
    7, 2, 18, 16, 14, 0]
private def pivots19 : Array (Fin 6) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0]

theorem card19 : Realized 6 19 := by
  apply (SmallSixNumbers.model 2 (by exact (show Nat.Prime 2 by decide).not_isSquare)).certify
    (fun i x => alphabet19[(words19[i.val]! / 8 ^ x.val) % 8]!)
    (fun p => slots19[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (SmallSixNumbers.model 2 (by exact (show Nat.Prime 2 by decide).not_isSquare)).distinct_of_pivots (fun i => pivots19[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card19


private def alphabet20 : Array ℤ :=
  #[-36, -20, -15, -5, -3, 0,
    1, 3, 4, 5, 12, 15,
    20, 36, 48]
private def words20 : Array ℕ :=
  #[4118705, 4827455, 4071455, 4068305, 4068055, 4068159, 4067858, 4064750, 4100156, 4056568, 4068095, 4068081, 6447455,
    3460580, 4062455, 4085855, 4068757, 4078235, 4050672, 4087154]
private def labels20 : Array (Fin 20) :=
  #[0, 1, 2, 3, 4, 5,
    1, 0, 6, 7, 8, 9,
    10, 11, 12, 13, 14, 15,
    16, 17, 13, 12, 18, 19,
    2, 3, 10, 11, 12, 13,
    6, 7, 16, 17, 13, 12]
private def pivots20 : Array (Fin 6) :=
  #[4, 5, 3, 2, 0, 0, 0, 1, 0, 0, 1, 0, 4,
    4, 2, 2, 0, 1, 0, 0]

theorem card20 : Realized 6 20 := by
  apply integerModel.certify
    (fun i x => alphabet20[(words20[i.val]! / 15 ^ x.val) % 15]!)
    (fun p => labels20[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots20[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card20


private def alphabet21 : Array IQ := #[(-1, 0), (0, -1), (0, 1), (1, 0)]
private def words21 : Array ℕ := #[4095, 399, 567, 3363, 1731, 2139, 1071, 2655, 2535, 275, 4027, 219, 3755,
    3359, 1859, 867, 3539, 1079, 3603, 2439, 751]
private def slots21 : Array (Fin 21) := #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 4, 9, 10,
    11, 12, 13, 2, 8, 14,
    15, 16, 12, 1, 7, 17,
    18, 15, 11, 0, 6, 19,
    19, 17, 14, 5, 10, 20]
private def pivots21 : Array (Fin 6) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

theorem card21 : Realized 6 21 := by
  apply (imaginaryModel 1 (by decide)).certify
    (fun i x => alphabet21[(words21[i.val]! / 4 ^ x.val) % 4]!)
    (fun p => slots21[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 1 (by decide)).distinct_of_pivots (fun i => pivots21[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card21


private def alphabet22 : Array ℤ :=
  #[-36, -20, -15, -5, -3, 0,
    1, 3, 4, 5, 12, 15,
    20, 36, 48]
private def words22 : Array ℕ :=
  #[4118705, 4827455, 4071455, 4068305, 4068055, 4068159, 4067858, 4064750, 4100156, 4056568, 4068095, 4068081, 6447455,
    3460580, 4062455, 4085855, 4068757, 4078235, 4050672, 4087154, 8067455, 2802455]
private def labels22 : Array (Fin 22) :=
  #[0, 1, 2, 3, 4, 5,
    1, 0, 6, 7, 8, 9,
    10, 11, 12, 13, 14, 15,
    16, 17, 13, 12, 18, 19,
    2, 3, 10, 11, 20, 21,
    6, 7, 16, 17, 21, 20]
private def pivots22 : Array (Fin 6) :=
  #[4, 5, 3, 2, 0, 0, 0, 1, 0, 0, 1, 0, 4,
    4, 2, 2, 0, 1, 0, 0, 4, 4]

theorem card22 : Realized 6 22 := by
  apply integerModel.certify
    (fun i x => alphabet22[(words22[i.val]! / 15 ^ x.val) % 15]!)
    (fun p => labels22[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots22[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card22

end SmallSix
