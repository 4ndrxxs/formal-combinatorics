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

private def alphabet30 : Array IQ := #[(-2, 0), (-1, -1), (-1, 0), (-1, 1), (1, -1), (1, 0), (1, 1),
    (2, 0)]
private def words30 : Array ℕ := #[187245, 111231, 104399, 48847, 63071, 234207, 75117, 150655, 158159, 213199, 198751, 27871, 48735,
    259711, 106495, 112335, 62415, 213087, 2175, 156159, 149711, 200143, 106191, 46815, 261727, 235519,
    155855, 215263, 95, 27135]
private def slots30 : Array (Fin 30) := #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 9, 10, 11,
    12, 5, 13, 14, 15, 16,
    17, 11, 18, 19, 20, 21,
    22, 16, 23, 24, 25, 1,
    26, 21, 27, 28, 29, 7]
private def pivots30 : Array (Fin 6) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0]

theorem card30 : Realized 6 30 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet30[(words30[i.val]! / 8 ^ x.val) % 8]!)
    (fun p => slots30[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots30[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card30


private def alphabet31 : Array IQ := #[(-1, 0), (0, -1), (0, 1), (1, 0)]
private def words31 : Array ℕ := #[4095, 2079, 231, 915, 3363, 1611, 1071, 2823, 2163, 1731, 411, 219, 1803,
    3207, 567, 2403, 867, 1203, 3147, 399, 2583, 3603, 2499, 315, 591, 1191,
    2439, 615, 1683, 1323, 2139]
private def slots31 : Array (Fin 31) := #[0, 1, 2, 3, 4, 5,
    6, 0, 7, 8, 9, 10,
    11, 12, 0, 13, 14, 15,
    16, 17, 18, 0, 19, 20,
    21, 22, 23, 24, 0, 25,
    26, 27, 28, 29, 30, 0]
private def pivots31 : Array (Fin 6) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0]

theorem card31 : Realized 6 31 := by
  apply (imaginaryModel 1 (by decide)).certify
    (fun i x => alphabet31[(words31[i.val]! / 4 ^ x.val) % 4]!)
    (fun p => slots31[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 1 (by decide)).distinct_of_pivots (fun i => pivots31[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card31


private def alphabet32 : Array IQ := #[(-2, 0), (-1, -1), (-1, 0), (-1, 1), (1, -1), (1, 0), (1, 1),
    (2, 0)]
private def words32 : Array ℕ := #[187245, 76461, 104399, 157199, 25375, 234207, 75117, 185517, 158159, 104463, 236831, 27871, 48735,
    216991, 259711, 1983, 197135, 62415, 213087, 45471, 2175, 260543, 64527, 200143, 19663, 245007,
    131295, 127263, 242383, 17167, 130783, 134943]
private def slots32 : Array (Fin 32) := #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17,
    18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 21, 20,
    28, 29, 30, 31, 15, 14]
private def pivots32 : Array (Fin 6) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0]

theorem card32 : Realized 6 32 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet32[(words32[i.val]! / 8 ^ x.val) % 8]!)
    (fun p => slots32[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots32[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card32


private def alphabet33 : Array IQ := #[(-1, 0), (0, -1), (0, 1), (1, 0)]
private def words33 : Array ℕ := #[4095, 543, 231, 3219, 1827, 2379, 1071, 2559, 2823, 1907, 195, 3739, 219,
    3339, 903, 2103, 1635, 867, 3763, 3147, 255, 2959, 1303, 3603, 315, 3407,
    1791, 2983, 2439, 1895, 1683, 2603, 3419]
private def slots33 : Array (Fin 33) := #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 9, 10, 11,
    12, 13, 0, 14, 15, 16,
    17, 18, 19, 20, 21, 22,
    23, 10, 24, 25, 26, 27,
    28, 29, 30, 31, 32, 20]
private def pivots33 : Array (Fin 6) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0]

theorem card33 : Realized 6 33 := by
  apply (imaginaryModel 1 (by decide)).certify
    (fun i x => alphabet33[(words33[i.val]! / 4 ^ x.val) % 4]!)
    (fun p => slots33[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 1 (by decide)).distinct_of_pivots (fun i => pivots33[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card33


private def alphabet34 : Array SmallSixNumbers.Quad := #[((-2, 0), (0, 0)), ((0, -1), (0, -1)), ((0, -1), (0, 1)), ((0, 0), (-2, 0)), ((0, 0), (2, 0)), ((0, 1), (0, -1)), ((0, 1), (0, 1)),
    ((2, 0), (0, 0))]
private def words34 : Array ℕ := #[262143, 16639, 197407, 73031, 60039, 177191, 98623, 147455, 195615, 222087, 70727, 51943, 7399,
    250407, 59391, 182367, 212895, 73991, 206215, 102503, 245567, 149247, 22879, 205639, 40007, 154023,
    30463, 257695, 152607, 125727, 77511, 32935, 194919, 202751]
private def slots34 : Array (Fin 34) := #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17,
    4, 18, 19, 20, 21, 22,
    23, 24, 25, 26, 6, 27,
    28, 29, 30, 31, 32, 33]
private def pivots34 : Array (Fin 6) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

theorem card34 : Realized 6 34 := by
  apply (SmallSixNumbers.model 2 (by exact (show Nat.Prime 2 by decide).not_isSquare)).certify
    (fun i x => alphabet34[(words34[i.val]! / 8 ^ x.val) % 8]!)
    (fun p => slots34[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (SmallSixNumbers.model 2 (by exact (show Nat.Prime 2 by decide).not_isSquare)).distinct_of_pivots (fun i => pivots34[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card34


private def alphabet35 : Array SmallSixNumbers.Quad := #[((-2, 0), (0, 0)), ((-1, 0), (0, -1)), ((-1, 0), (0, 1)), ((0, -1), (-1, 0)), ((0, -1), (1, 0)), ((0, 0), (-2, 0)), ((0, 0), (2, 0)),
    ((0, 1), (-1, 0)), ((0, 1), (1, 0)), ((1, 0), (0, -1)), ((1, 0), (0, 1)), ((2, 0), (0, 0))]
private def words35 : Array ℕ := #[2985983, 125279, 2490983, 1034363, 468875, 1852499, 1245167, 1617407, 1987271, 2698859, 1023131, 386147, 76835,
    2929043, 425087, 1876823, 2612519, 1037675, 928235, 2036747, 1306883, 2860847, 1626911, 198359, 2038619, 822971,
    1691219, 237599, 2922407, 1683143, 1426535, 1056539, 249491, 1981379, 2560895]
private def slots35 : Array (Fin 35) := #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17,
    18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 6, 28,
    29, 30, 31, 32, 33, 34]
private def pivots35 : Array (Fin 6) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem card35 : Realized 6 35 := by
  apply (SmallSixNumbers.model 3 (by exact (show Nat.Prime 3 by decide).not_isSquare)).certify
    (fun i x => alphabet35[(words35[i.val]! / 12 ^ x.val) % 12]!)
    (fun p => slots35[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (SmallSixNumbers.model 3 (by exact (show Nat.Prime 3 by decide).not_isSquare)).distinct_of_pivots (fun i => pivots35[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card35


private def alphabet36 : Array IQ := #[(-2, 0), (-1, -1), (-1, 0), (-1, 1), (1, -1), (1, 0), (1, 1),
    (2, 0)]
private def words36 : Array ℕ := #[187245, 76461, 104399, 157199, 46047, 213535, 75117, 185517, 158159, 104463, 216543, 48159, 48735,
    216991, 259711, 1983, 102991, 156559, 213087, 45471, 2175, 260543, 158799, 105871, 106191, 159503,
    46815, 214815, 258815, 831, 155855, 102671, 215263, 47391, 3327, 261439]
private def slots36 : Array (Fin 36) := #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16, 17,
    18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29,
    30, 31, 32, 33, 34, 35]
private def pivots36 : Array (Fin 6) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem card36 : Realized 6 36 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet36[(words36[i.val]! / 8 ^ x.val) % 8]!)
    (fun p => slots36[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots36[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card36

end SmallSix
