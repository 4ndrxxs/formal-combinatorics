module
public import Quantum.Pivots
public import Quantum.Biquadratic
/-! Explicit projective-ray certificates of order seven. -/
@[expose] public section
namespace SmallSeven
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet7 : Array ℤ :=
  #[0, 1]
private def words7 : Array ℕ :=
  #[64, 1, 2, 4, 8, 32, 16]
private def labels7 : Array (Fin 7) :=
  #[0, 1, 2, 3, 4, 5, 6,
    4, 2, 0, 6, 5, 1, 3,
    2, 6, 3, 5, 1, 0, 4,
    5, 0, 4, 2, 3, 6, 1,
    1, 3, 5, 4, 6, 2, 0,
    3, 5, 6, 1, 0, 4, 2,
    6, 4, 1, 0, 2, 3, 5]
private def pivots7 : Array (Fin 7) :=
  #[6, 0, 1, 2, 3, 5, 4]

theorem card7 : Realized 7 7 := by
  apply integerModel.certify
    (fun i x => alphabet7[(words7[i.val]! / 2 ^ x.val) % 2]!)
    (fun p => labels7[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots7[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card7


private def alphabet9 : Array ℤ :=
  #[-96, -75, -8, 0, 1, 8,
    15, 40, 85, 180, 204]
private def words9 : Array ℕ :=
  #[7617712, 5846152, 5846162, 5846272, 6331966, 5689093, 5860792, 5371039, 6487770]
private def labels9 : Array (Fin 9) :=
  #[0, 1, 2, 3, 4, 5, 6,
    4, 7, 0, 6, 8, 1, 3,
    2, 6, 3, 5, 1, 0, 4,
    5, 0, 4, 2, 3, 6, 1,
    1, 3, 5, 4, 6, 2, 0,
    3, 8, 6, 1, 0, 4, 7,
    6, 4, 1, 0, 7, 3, 8]
private def pivots9 : Array (Fin 7) :=
  #[6, 0, 1, 2, 3, 3, 4, 1, 1]

theorem card9 : Realized 7 9 := by
  apply integerModel.certify
    (fun i x => alphabet9[(words9[i.val]! / 11 ^ x.val) % 11]!)
    (fun p => labels9[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots9[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card9


private def alphabet10 : Array ℤ :=
  #[-2, 0, 1, 2]
private def words10 : Array ℕ :=
  #[15957, 2901, 9045, 5465, 5477, 5525, 5462, 5717, 6485, 9557]
private def labels10 : Array (Fin 10) :=
  #[0, 1, 2, 3, 4, 5, 6,
    1, 2, 0, 4, 5, 6, 3,
    2, 0, 1, 5, 6, 3, 4,
    3, 4, 5, 6, 7, 8, 9,
    4, 5, 6, 7, 3, 9, 8,
    5, 6, 3, 8, 9, 4, 7,
    6, 3, 4, 9, 8, 7, 5]
private def pivots10 : Array (Fin 7) :=
  #[4, 4, 4, 1, 2, 3, 0, 4, 5, 6]

theorem card10 : Realized 7 10 := by
  apply integerModel.certify
    (fun i x => alphabet10[(words10[i.val]! / 4 ^ x.val) % 4]!)
    (fun p => labels10[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots10[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card10


private def alphabet11 : Array ℤ :=
  #[-96, -75, -8, -5, 0, 1,
    5, 8, 12, 15, 40, 85,
    180, 204]
private def words11 : Array ℕ :=
  #[39964460, 32434925, 32434938, 32435120, 35132276, 31372996, 32473340, 30305678, 35653762, 32397292, 32588980]
private def labels11 : Array (Fin 11) :=
  #[0, 1, 2, 3, 4, 5, 6,
    4, 7, 0, 6, 8, 1, 3,
    2, 9, 10, 5, 1, 0, 4,
    5, 0, 4, 2, 10, 9, 1,
    1, 10, 5, 4, 9, 2, 0,
    10, 8, 9, 1, 0, 4, 7,
    9, 4, 1, 0, 7, 10, 8]
private def pivots11 : Array (Fin 7) :=
  #[6, 0, 1, 2, 3, 3, 4, 1, 1, 2, 2]

theorem card11 : Realized 7 11 := by
  apply integerModel.certify
    (fun i x => alphabet11[(words11[i.val]! / 14 ^ x.val) % 14]!)
    (fun p => labels11[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots11[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card11


private def alphabet12 : Array ℤ :=
  #[-20, -3, 0, 1, 3, 4,
    9, 12, 15, 16]
private def words12 : Array ℕ :=
  #[2522422, 2222232, 3222222, 2223222, 2222223, 2122522, 2232222, 272226, 2212225, 8292227, 2222322, 2322222]
private def labels12 : Array (Fin 12) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 8, 0, 9, 5, 3, 1,
    1, 10, 4, 11, 6, 2, 3,
    5, 3, 6, 1, 0, 4, 2,
    3, 11, 1, 10, 2, 6, 4,
    9, 7, 5, 8, 3, 1, 0,
    8, 9, 3, 7, 1, 0, 5]
private def pivots12 : Array (Fin 7) :=
  #[2, 1, 6, 3, 0, 2, 4, 0, 0, 0, 2, 5]

theorem card12 : Realized 7 12 := by
  apply integerModel.certify
    (fun i x => alphabet12[(words12[i.val]! / 10 ^ x.val) % 10]!)
    (fun p => labels12[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots12[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card12


private def alphabet13 : Array ℤ :=
  #[-120, -96, -75, -8, -5, 0,
    1, 5, 8, 12, 15, 40,
    64, 85, 136, 180, 204, 225,
    255]
private def words13 : Array ℕ :=
  #[295343586, 248297706, 248297724, 248298066, 260698777, 243379802, 248428026, 238462051, 263133931, 235999689, 248168828, 248819711, 265596350]
private def labels13 : Array (Fin 13) :=
  #[0, 1, 2, 3, 4, 5, 6,
    4, 7, 0, 6, 8, 1, 3,
    9, 10, 11, 12, 1, 0, 4,
    12, 0, 4, 9, 11, 10, 1,
    1, 11, 5, 4, 10, 2, 0,
    11, 8, 10, 1, 0, 4, 7,
    10, 4, 1, 0, 7, 11, 8]
private def pivots13 : Array (Fin 7) :=
  #[6, 0, 1, 2, 3, 3, 4, 1, 1, 1, 2, 2, 1]

theorem card13 : Realized 7 13 := by
  apply integerModel.certify
    (fun i x => alphabet13[(words13[i.val]! / 19 ^ x.val) % 19]!)
    (fun p => labels13[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots13[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card13


private def alphabet14 : Array ℤ :=
  #[-220, -24, -21, -8, -7, 0,
    1, 7, 8, 15, 21, 24,
    220]
private def words14 : Array ℕ :=
  #[28377367, 25787104, 26145216, 26145228, 26173776, 45452958, 16492273, 26074911, 26356127, 24660069, 26887879, 26516508, 26156207,
    26134235]
private def labels14 : Array (Fin 14) :=
  #[0, 1, 2, 3, 4, 5, 6,
    6, 2, 7, 8, 5, 9, 10,
    2, 5, 8, 7, 6, 10, 9,
    1, 0, 6, 2, 3, 4, 5,
    3, 4, 5, 11, 12, 6, 13,
    5, 3, 11, 6, 13, 12, 4,
    4, 6, 3, 5, 11, 13, 12]
private def pivots14 : Array (Fin 7) :=
  #[3, 3, 0, 1, 4, 2, 2, 3, 3, 1, 1, 5, 0,
    0]

theorem card14 : Realized 7 14 := by
  apply integerModel.certify
    (fun i x => alphabet14[(words14[i.val]! / 13 ^ x.val) % 13]!)
    (fun p => labels14[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots14[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card14


private def alphabet15 : Array ℤ :=
  #[-120, -96, -75, -40, -8, -5,
    0, 1, 5, 8, 12, 15,
    40, 64, 85, 96, 136, 180,
    204, 225, 255]
private def words15 : Array ℕ :=
  #[626092683, 585335030, 540326583, 540327003, 523962387, 532204665, 540521043, 560774850, 520008096, 564794376, 540326563, 515942559, 540133845,
    541105368, 568859997]
private def labels15 : Array (Fin 15) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 8, 0, 6, 9, 10, 3,
    11, 12, 13, 14, 1, 0, 4,
    14, 0, 4, 11, 13, 12, 1,
    10, 13, 5, 7, 12, 2, 0,
    13, 9, 12, 10, 0, 7, 8,
    12, 4, 1, 0, 8, 13, 9]
private def pivots15 : Array (Fin 7) :=
  #[6, 0, 1, 2, 0, 3, 4, 3, 1, 1, 0, 1, 2,
    2, 1]

theorem card15 : Realized 7 15 := by
  apply integerModel.certify
    (fun i x => alphabet15[(words15[i.val]! / 21 ^ x.val) % 21]!)
    (fun p => labels15[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots15[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card15


private def alphabet16 : Array ℤ :=
  #[-24, -8, -7, 0, 1, 7,
    8, 15, 24]
private def words16 : Array ℕ :=
  #[2090316, 1738209, 1793614, 1793622, 1800174, 1793694, 2325054, 731055, 1822044, 1783407, 3919620, 1616484, 1911756,
    1852662, 1791428, 1795076]
private def labels16 : Array (Fin 16) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 2, 8, 9, 10, 11, 12,
    2, 10, 9, 8, 7, 12, 11,
    1, 0, 6, 2, 3, 4, 5,
    3, 4, 5, 13, 14, 6, 15,
    10, 3, 13, 7, 15, 14, 4,
    4, 7, 3, 10, 13, 15, 14]
private def pivots16 : Array (Fin 7) :=
  #[3, 3, 0, 1, 4, 2, 6, 2, 3, 3, 2, 1, 1,
    5, 0, 0]

theorem card16 : Realized 7 16 := by
  apply integerModel.certify
    (fun i x => alphabet16[(words16[i.val]! / 9 ^ x.val) % 9]!)
    (fun p => labels16[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots16[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card16

end SmallSeven
