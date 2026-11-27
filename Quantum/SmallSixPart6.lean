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

private def alphabet6 : Array ℤ :=
  #[0, 1]
private def words6 : Array ℕ :=
  #[4, 1, 16, 2, 8, 32]
private def labels6 : Array (Fin 6) :=
  #[0, 1, 2, 3, 4, 5,
    1, 2, 5, 4, 3, 0,
    3, 4, 0, 2, 5, 1,
    4, 0, 3, 5, 1, 2,
    5, 3, 1, 0, 2, 4,
    2, 5, 4, 1, 0, 3]
private def pivots6 : Array (Fin 6) :=
  #[2, 0, 4, 1, 3, 5]

theorem card6 : Realized 6 6 := by
  apply integerModel.certify
    (fun i x => alphabet6[(words6[i.val]! / 2 ^ x.val) % 2]!)
    (fun p => labels6[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots6[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card6


private def alphabet8 : Array ℤ :=
  #[-3, 0, 1, 3, 4]
private def words8 : Array ℕ :=
  #[3931, 13283, 4531, 3911, 4031, 784, 3907, 7031]
private def labels8 : Array (Fin 8) :=
  #[0, 1, 2, 3, 4, 5,
    6, 2, 7, 4, 3, 0,
    3, 4, 0, 2, 5, 1,
    4, 0, 3, 5, 1, 2,
    7, 3, 6, 0, 2, 4,
    2, 5, 4, 1, 0, 3]
private def pivots8 : Array (Fin 6) :=
  #[2, 0, 4, 1, 3, 0, 0, 5]

theorem card8 : Realized 6 8 := by
  apply integerModel.certify
    (fun i x => alphabet8[(words8[i.val]! / 5 ^ x.val) % 5]!)
    (fun p => labels8[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots8[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card8


private def alphabet9 : Array ℤ :=
  #[-52, -48, -36, 0, 1, 5,
    12, 15, 20, 39]
private def words9 : Array ℕ :=
  #[334333, 353363, 333334, 433333, 313983, 323073, 333433, 333343, 343333]
private def labels9 : Array (Fin 9) :=
  #[0, 1, 2, 3, 4, 5,
    2, 4, 3, 0, 5, 1,
    6, 0, 7, 8, 2, 3,
    3, 5, 0, 2, 1, 4,
    7, 2, 8, 6, 3, 0,
    8, 3, 6, 7, 0, 2]
private def pivots9 : Array (Fin 6) :=
  #[3, 1, 0, 5, 1, 1, 2, 1, 4]

theorem card9 : Realized 6 9 := by
  apply integerModel.certify
    (fun i x => alphabet9[(words9[i.val]! / 10 ^ x.val) % 10]!)
    (fun p => labels9[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots9[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card9


private def alphabet10 : Array ℤ :=
  #[-5, -3, 0, 1, 3, 4,
    5, 12]
private def words10 : Array ℕ :=
  #[74962, 173204, 78994, 74906, 75410, 42133, 74899, 67026, 107666, 95634]
private def labels10 : Array (Fin 10) :=
  #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 4, 3, 9,
    3, 4, 0, 2, 5, 1,
    4, 9, 3, 5, 1, 7,
    8, 3, 6, 0, 2, 4,
    2, 5, 4, 1, 0, 3]
private def pivots10 : Array (Fin 6) :=
  #[2, 0, 4, 1, 3, 0, 0, 2, 5, 2]

theorem card10 : Realized 6 10 := by
  apply integerModel.certify
    (fun i x => alphabet10[(words10[i.val]! / 8 ^ x.val) % 8]!)
    (fun p => labels10[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots10[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card10


private def alphabet11 : Array ℤ :=
  #[-15, -12, -4, 0, 1, 3,
    4, 5, 8, 12, 15]
private def words11 : Array ℕ :=
  #[560783, 1176398, 516849, 531469, 209850, 532799, 531530, 692519, 531589, 546109, 531440]
private def labels11 : Array (Fin 11) :=
  #[0, 1, 2, 3, 4, 5,
    5, 6, 7, 8, 9, 10,
    7, 10, 8, 5, 6, 9,
    3, 4, 0, 2, 5, 1,
    8, 9, 5, 7, 10, 6,
    2, 5, 3, 0, 1, 4]
private def pivots11 : Array (Fin 6) :=
  #[1, 2, 1, 0, 2, 3, 0, 5, 2, 4, 0]

theorem card11 : Realized 6 11 := by
  apply integerModel.certify
    (fun i x => alphabet11[(words11[i.val]! / 11 ^ x.val) % 11]!)
    (fun p => labels11[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots11[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card11


private def alphabet12 : Array ℤ :=
  #[-7, -5, -3, 0, 1, 3,
    4, 5, 7, 12, 24]
private def words12 : Array ℕ :=
  #[531589, 1014623, 546109, 540840, 527552, 370420, 531469, 502912, 692519, 619798, 531479, 532799]
private def labels12 : Array (Fin 12) :=
  #[0, 1, 2, 3, 4, 5,
    6, 7, 8, 4, 3, 9,
    10, 11, 0, 2, 5, 1,
    11, 9, 10, 5, 1, 7,
    8, 10, 6, 0, 2, 11,
    2, 5, 11, 1, 0, 10]
private def pivots12 : Array (Fin 6) :=
  #[2, 0, 4, 1, 1, 0, 0, 2, 5, 2, 1, 3]

theorem card12 : Realized 6 12 := by
  apply integerModel.certify
    (fun i x => alphabet12[(words12[i.val]! / 11 ^ x.val) % 11]!)
    (fun p => labels12[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots12[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card12


private def alphabet13 : Array ℤ :=
  #[-119, -75, -48, -36, -32, -24,
    -12, -4, 0, 1, 3, 4,
    7, 8, 9, 12, 24, 25,
    119, 120]
private def words13 : Array ℕ :=
  #[26955368, 27107368, 33348568, 26947456, 26947312, 23748168, 26947369, 25667588, 28707568, 20589768, 14094568, 10945148, 33348708]
private def labels13 : Array (Fin 13) :=
  #[0, 1, 2, 3, 4, 5,
    5, 6, 7, 0, 2, 8,
    6, 9, 8, 2, 10, 7,
    11, 12, 10, 1, 9, 6,
    12, 11, 6, 5, 1, 0,
    1, 10, 9, 4, 3, 2]
private def pivots13 : Array (Fin 6) :=
  #[3, 4, 2, 0, 0, 2, 0, 1, 1, 2, 2, 1, 1]

theorem card13 : Realized 6 13 := by
  apply integerModel.certify
    (fun i x => alphabet13[(words13[i.val]! / 20 ^ x.val) % 20]!)
    (fun p => labels13[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots13[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card13


private def alphabet14 : Array ℤ :=
  #[-24, -7, -5, 0, 1, 5,
    7, 12, 24]
private def words14 : Array ℕ :=
  #[201522, 205851, 494538, 199371, 81197, 197130, 435488, 200019, 199299, 140245, 258339, 199291, 219378,
    179850]
private def labels14 : Array (Fin 14) :=
  #[0, 1, 2, 3, 4, 5,
    1, 6, 3, 7, 8, 9,
    10, 8, 7, 11, 12, 13,
    3, 9, 1, 8, 7, 6,
    11, 7, 8, 10, 13, 12,
    5, 3, 4, 1, 2, 0]
private def pivots14 : Array (Fin 6) :=
  #[1, 4, 0, 2, 0, 1, 0, 3, 1, 0, 5, 0, 2,
    2]

theorem card14 : Realized 6 14 := by
  apply integerModel.certify
    (fun i x => alphabet14[(words14[i.val]! / 9 ^ x.val) % 9]!)
    (fun p => labels14[p.1.val * 6 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots14[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card14

end SmallSix
