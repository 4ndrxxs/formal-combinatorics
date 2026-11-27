module
public import Quantum.Pivots
public import Quantum.Biquadratic
/-! Explicit projective-ray certificates of order seven. -/
@[expose] public section
namespace SmallSeven
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet17 : Array ℤ :=
  #[-312, -120, -96, -75, -40, -35,
    -8, -5, 0, 1, 5, 8,
    12, 15, 40, 64, 84, 85,
    91, 96, 136, 180, 204, 225,
    255, 288]
private def words17 : Array ℕ :=
  #[2879095032, 2724830489, 2570179282, 2570179932, 2510702086, 2546504384, 2570636232, 2629638864, 2499119722, 2641379996, 2570179257, 2487273576, 97487528,
    2572008512, 2653226272, 5656149676, 2569724984]
private def labels17 : Array (Fin 17) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 8, 0, 6, 9, 10, 3,
    11, 12, 13, 14, 1, 15, 4,
    14, 15, 4, 11, 13, 12, 1,
    10, 13, 5, 7, 16, 2, 0,
    13, 9, 16, 10, 0, 7, 8,
    16, 4, 1, 0, 8, 13, 9]
private def pivots17 : Array (Fin 7) :=
  #[6, 0, 1, 2, 0, 3, 4, 3, 1, 1, 0, 1, 2,
    2, 1, 2, 2]

theorem card17 : Realized 7 17 := by
  apply integerModel.certify
    (fun i x => alphabet17[(words17[i.val]! / 26 ^ x.val) % 26]!)
    (fun p => labels17[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots17[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card17


private def alphabet18 : Array ℤ :=
  #[-104, -56, -44, -24, -15, -12,
    -7, 0, 1, 5, 7, 8,
    15, 24, 33, 40, 44, 56,
    75, 96, 117, 180, 195]
private def words18 : Array ℕ :=
  #[1084475560, 1089789894, 1083293015, 1083511929, 1083353552, 1231389440, 1082516144, 1083426622, 1083341522, 1083353507, 1083354080, 1083633392, 1083536252,
    1083268649, 2183968204, 240192618, 1529140264, 492049518]
private def labels18 : Array (Fin 18) :=
  #[0, 1, 2, 3, 4, 5, 6,
    6, 7, 4, 5, 8, 1, 0,
    9, 10, 1, 11, 5, 12, 13,
    14, 4, 3, 2, 11, 10, 15,
    15, 8, 10, 4, 7, 11, 14,
    13, 16, 17, 10, 1, 9, 12,
    12, 17, 16, 1, 10, 13, 9]
private def pivots18 : Array (Fin 7) :=
  #[2, 5, 1, 1, 0, 6, 2, 1, 1, 0, 2, 4, 0,
    0, 5, 5, 4, 4]

theorem card18 : Realized 7 18 := by
  apply integerModel.certify
    (fun i x => alphabet18[(words18[i.val]! / 23 ^ x.val) % 23]!)
    (fun p => labels18[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots18[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card18


private def alphabet19 : Array ℤ :=
  #[-39, -24, -5, -4, -3, 0,
    1, 3, 4, 5, 7, 12,
    15, 20, 24, 36, 48, 52]
private def words19 : Array ℕ :=
  #[180099779, 248404091, 180047327, 189512564, 112250219, 172506448, 180065039, 181954283, 180064716, 282311339, 146367419, 180070547, 180169691,
    214076939, 180064733, 183843854, 176285581, 180127391, 180127049]
private def labels19 : Array (Fin 19) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 6, 0, 2, 8, 9, 10,
    8, 11, 12, 13, 7, 6, 14,
    6, 15, 13, 12, 2, 0, 16,
    2, 16, 15, 17, 18, 10, 9,
    1, 4, 16, 18, 17, 2, 15,
    4, 14, 6, 5, 1, 3, 11]
private def pivots19 : Array (Fin 7) :=
  #[1, 4, 1, 0, 4, 0, 2, 5, 0, 4, 4, 3, 4,
    6, 1, 0, 0, 1, 1]

theorem card19 : Realized 7 19 := by
  apply integerModel.certify
    (fun i x => alphabet19[(words19[i.val]! / 18 ^ x.val) % 18]!)
    (fun p => labels19[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots19[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card19


private def alphabet20 : Array ℤ :=
  #[-56, -24, -15, -12, -7, -3,
    0, 1, 3, 4, 5, 7,
    8, 12, 15, 24, 33, 56]
private def words20 : Array ℕ :=
  #[216710106, 217967226, 216095190, 216071880, 216077659, 250089882, 215659698, 216130236, 216066156, 216077608, 216077982, 216182634, 216077737,
    216083490, 576985146, 30899994, 387083562, 46541418, 208521330, 227417658]
private def labels20 : Array (Fin 20) :=
  #[0, 1, 2, 3, 4, 5, 6,
    6, 7, 4, 5, 8, 1, 0,
    9, 10, 1, 11, 5, 12, 13,
    14, 4, 3, 2, 11, 10, 15,
    15, 8, 10, 4, 7, 11, 14,
    13, 16, 17, 18, 19, 9, 12,
    12, 17, 16, 19, 18, 13, 9]
private def pivots20 : Array (Fin 7) :=
  #[2, 5, 1, 1, 0, 6, 2, 1, 1, 0, 2, 4, 0,
    3, 5, 5, 4, 4, 2, 2]

theorem card20 : Realized 7 20 := by
  apply integerModel.certify
    (fun i x => alphabet20[(words20[i.val]! / 18 ^ x.val) % 18]!)
    (fun p => labels20[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots20[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card20


private def alphabet21 : Array ℤ :=
  #[-16, -15, -12, -7, -4, -3,
    0, 1, 3, 4, 5, 7,
    8, 12, 15, 16, 24, 63]
private def words21 : Array ℕ :=
  #[235002498, 210467274, 216077659, 12007878, 590215038, 216182634, 216077676, 182380362, 216077046, 216078360, 217967226, 216083490, 318324282,
    216077982, 206664810, 215657826, 216497688, 250089882, 227461722, 216076696, 216080903]
private def labels21 : Array (Fin 21) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 8, 9, 10, 2, 11, 12,
    12, 9, 8, 2, 11, 10, 7,
    13, 2, 14, 15, 16, 17, 18,
    6, 17, 5, 11, 10, 19, 20,
    1, 0, 17, 16, 15, 20, 19,
    2, 5, 18, 4, 3, 6, 14]
private def pivots21 : Array (Fin 7) :=
  #[3, 3, 0, 2, 2, 4, 1, 4, 1, 1, 5, 3, 4,
    2, 3, 1, 1, 6, 3, 0, 0]

theorem card21 : Realized 7 21 := by
  apply integerModel.certify
    (fun i x => alphabet21[(words21[i.val]! / 18 ^ x.val) % 18]!)
    (fun p => labels21[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots21[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card21


private def alphabet22 : Array ℤ :=
  #[-4, -3, -2, -1, 0, 1,
    2, 3, 4]
private def words22 : Array ℕ :=
  #[3579025, 1400773, 2817949, 2393842, 2392700, 2390784, 2391550, 2390143, 2392379, 2388551, 2391171, 2392060, 2389946,
    2392206, 2391584, 2391485, 2398045, 2450533, 2922925, 2391493, 2391565, 2392213]
private def labels22 : Array (Fin 22) :=
  #[0, 1, 2, 3, 4, 5, 6,
    1, 2, 0, 7, 8, 9, 10,
    2, 0, 1, 11, 12, 13, 14,
    3, 7, 11, 15, 16, 17, 18,
    4, 8, 12, 16, 19, 18, 17,
    5, 9, 13, 17, 18, 20, 16,
    6, 10, 14, 18, 17, 16, 21]
private def pivots22 : Array (Fin 7) :=
  #[4, 4, 4, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0,
    0, 0, 0, 4, 5, 6, 1, 2, 3]

theorem card22 : Realized 7 22 := by
  apply integerModel.certify
    (fun i x => alphabet22[(words22[i.val]! / 9 ^ x.val) % 9]!)
    (fun p => labels22[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots22[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card22


private def alphabet23 : Array ℤ :=
  #[-4, -3, -2, -1, 0, 1,
    2, 3, 4]
private def words23 : Array ℕ :=
  #[4536931, 2450533, 823405, 2393842, 2392700, 2390784, 2391550, 2390143, 2392379, 2388551, 2391171, 2392060, 2389946,
    2392206, 2391584, 2391485, 2647363, 2240581, 2922925, 2398045, 2391493, 2391565, 2392213]
private def labels23 : Array (Fin 23) :=
  #[0, 1, 2, 3, 4, 5, 6,
    1, 2, 0, 7, 8, 9, 10,
    2, 0, 1, 11, 12, 13, 14,
    3, 7, 11, 15, 16, 17, 18,
    4, 8, 12, 19, 20, 18, 1,
    5, 9, 13, 1, 18, 21, 19,
    6, 10, 14, 18, 17, 16, 22]
private def pivots23 : Array (Fin 7) :=
  #[4, 5, 4, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0,
    0, 0, 0, 4, 4, 6, 4, 1, 2, 3]

theorem card23 : Realized 7 23 := by
  apply integerModel.certify
    (fun i x => alphabet23[(words23[i.val]! / 9 ^ x.val) % 9]!)
    (fun p => labels23[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots23[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card23

end SmallSeven
