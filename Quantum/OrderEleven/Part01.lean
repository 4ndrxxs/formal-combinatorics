module
public import Quantum.Pivots
public import Quantum.Biquadratic
/-! Explicit order-eleven quantum Latin squares, checked over the complex numbers. -/
@[expose] public section
namespace OrderEleven
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet11 : Array ℤ :=
  #[0, 1]
private def words11 : Array ℕ :=
  #[64, 128, 256, 512, 1024, 2, 4, 8, 16, 32, 1]
private def labels11 : Array (Fin 11) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    3, 4, 1, 2, 0, 6, 7, 8, 9, 10, 5,
    1, 3, 0, 4, 2, 7, 8, 9, 10, 5, 6,
    2, 0, 4, 1, 3, 8, 9, 10, 5, 6, 7,
    4, 2, 3, 0, 1, 9, 10, 5, 6, 7, 8,
    5, 6, 7, 8, 9, 10, 0, 2, 3, 4, 1,
    6, 7, 8, 9, 10, 2, 5, 4, 1, 3, 0,
    7, 8, 9, 10, 5, 4, 2, 6, 0, 1, 3,
    8, 9, 10, 5, 6, 0, 3, 1, 7, 2, 4,
    9, 10, 5, 6, 7, 3, 1, 0, 4, 8, 2,
    10, 5, 6, 7, 8, 1, 4, 3, 2, 0, 9]
private def pivots11 : Array (Fin 11) :=
  #[6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 0]

theorem card11 : Realized 11 11 := by
  apply integerModel.certify
    (fun i x => alphabet11[(words11[i.val]! / 2 ^ x.val) % 2]!)
    (fun p => labels11[p.1.val * 11 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots11[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card11


private def alphabet13 : Array ℤ :=
  #[-5, 0, 1, 5, 12]
private def words13 : Array ℕ :=
  #[12222656, 12285156, 12597656, 14160156, 21972656, 12207036, 12207056, 12207156, 12207656, 12210156, 12207032, 12216456, 12203981]
private def labels13 : Array (Fin 13) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    3, 4, 1, 2, 0, 6, 7, 8, 9, 10, 5,
    1, 3, 0, 4, 2, 7, 8, 9, 10, 5, 6,
    2, 0, 4, 1, 3, 8, 9, 10, 5, 6, 7,
    4, 2, 3, 0, 1, 9, 10, 5, 6, 7, 8,
    7, 11, 12, 5, 8, 10, 0, 2, 3, 4, 1,
    8, 12, 11, 7, 10, 2, 5, 4, 1, 3, 0,
    10, 5, 7, 8, 9, 4, 2, 6, 0, 1, 3,
    6, 8, 10, 9, 5, 0, 3, 1, 7, 2, 4,
    9, 7, 5, 10, 6, 3, 1, 0, 4, 8, 2,
    5, 10, 8, 6, 7, 1, 4, 3, 2, 0, 9]
private def pivots13 : Array (Fin 11) :=
  #[6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 0, 2, 2]

theorem card13 : Realized 11 13 := by
  apply integerModel.certify
    (fun i x => alphabet13[(words13[i.val]! / 5 ^ x.val) % 5]!)
    (fun p => labels13[p.1.val * 11 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots13[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card13


private def alphabet14 : Array ℤ :=
  #[-24, -12, 0, 1, 3, 4,
    8, 9, 32, 75]
private def words14 : Array ℕ :=
  #[22223222222, 22232222222, 22322222222, 23222222222, 32222222222, 22222222232, 22222222322, 22222223222, 22222232222, 22222322222, 22222222223, 22222222452, 22222222176,
    22222222809]
private def labels14 : Array (Fin 14) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    3, 4, 1, 2, 0, 6, 7, 8, 9, 10, 5,
    1, 3, 0, 4, 2, 7, 8, 9, 10, 5, 6,
    2, 0, 4, 1, 3, 8, 9, 10, 5, 6, 7,
    4, 2, 3, 0, 1, 9, 10, 5, 6, 7, 8,
    6, 5, 8, 9, 7, 10, 0, 2, 3, 4, 1,
    10, 6, 9, 7, 8, 2, 5, 4, 1, 3, 0,
    5, 10, 7, 8, 9, 4, 2, 6, 0, 1, 3,
    8, 9, 11, 12, 13, 0, 3, 1, 7, 2, 4,
    9, 7, 13, 11, 12, 3, 1, 0, 4, 8, 2,
    7, 8, 12, 13, 11, 1, 4, 3, 2, 0, 9]
private def pivots14 : Array (Fin 11) :=
  #[6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 0, 1, 0,
    0]

theorem card14 : Realized 11 14 := by
  apply integerModel.certify
    (fun i x => alphabet14[(words14[i.val]! / 10 ^ x.val) % 10]!)
    (fun p => labels14[p.1.val * 11 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots14[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card14


private def alphabet15 : Array ℤ :=
  #[-7, -5, 0, 1, 5, 7,
    12, 24]
private def words15 : Array ℕ :=
  #[2454529170, 2456364178, 2471044242, 2588484754, 3528008850, 2454267034, 2454267090, 2454267538, 2454271122, 2454299794, 2454267027, 2454398226, 2454234514,
    2454267069, 2454267015]
private def labels15 : Array (Fin 15) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    3, 4, 1, 2, 0, 6, 7, 8, 9, 10, 5,
    1, 3, 0, 4, 2, 7, 8, 9, 10, 5, 6,
    2, 0, 4, 1, 3, 8, 9, 10, 5, 6, 7,
    4, 2, 3, 0, 1, 9, 10, 5, 6, 7, 8,
    7, 11, 12, 5, 8, 10, 0, 2, 3, 4, 1,
    8, 12, 11, 7, 10, 2, 5, 4, 1, 3, 0,
    13, 14, 7, 8, 9, 4, 2, 6, 0, 1, 3,
    6, 8, 10, 9, 5, 0, 3, 1, 7, 2, 4,
    9, 7, 5, 10, 6, 3, 1, 0, 4, 8, 2,
    14, 13, 8, 6, 7, 1, 4, 3, 2, 0, 9]
private def pivots15 : Array (Fin 11) :=
  #[6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 0, 2, 2,
    0, 0]

theorem card15 : Realized 11 15 := by
  apply integerModel.certify
    (fun i x => alphabet15[(words15[i.val]! / 8 ^ x.val) % 8]!)
    (fun p => labels15[p.1.val * 11 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots15[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card15


private def alphabet16 : Array ℤ :=
  #[-24, -12, -7, 0, 1, 3,
    4, 7, 8, 9, 24, 32,
    75]
private def words16 : Array ℕ :=
  #[448044925318, 448102847026, 448855829230, 458644597882, 585898590358, 448040098522, 448040098678, 448040100706, 448040127070, 448040469802, 448040098510, 448042811804, 448039927143,
    448040098886, 448040098254, 448040099831]
private def labels16 : Array (Fin 16) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    3, 4, 1, 2, 0, 6, 7, 8, 9, 10, 5,
    1, 3, 0, 4, 2, 7, 8, 9, 10, 5, 6,
    2, 0, 4, 1, 3, 8, 9, 10, 5, 6, 7,
    4, 2, 3, 0, 1, 9, 10, 5, 6, 7, 8,
    6, 5, 11, 12, 7, 10, 0, 2, 3, 4, 1,
    10, 6, 12, 7, 11, 2, 5, 4, 1, 3, 0,
    5, 10, 7, 11, 12, 4, 2, 6, 0, 1, 3,
    8, 9, 13, 14, 15, 0, 3, 1, 7, 2, 4,
    9, 7, 15, 13, 14, 3, 1, 0, 4, 8, 2,
    7, 8, 14, 15, 13, 1, 4, 3, 2, 0, 9]
private def pivots16 : Array (Fin 11) :=
  #[6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 0, 4, 4,
    1, 0, 0]

theorem card16 : Realized 11 16 := by
  apply integerModel.certify
    (fun i x => alphabet16[(words16[i.val]! / 13 ^ x.val) % 13]!)
    (fun p => labels16[p.1.val * 11 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots16[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card16


private def alphabet17 : Array ℤ :=
  #[-2, -1, 0, 1, 2]
private def words17 : Array ℕ :=
  #[24429687, 24492187, 24804687, 26367187, 34179687, 24414067, 24414087, 24414187, 24414687, 24417187, 24414063, 24411197, 24420197,
    24407567, 24412763, 24413489, 24415289]
private def labels17 : Array (Fin 17) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    3, 4, 1, 2, 0, 6, 7, 8, 9, 10, 5,
    1, 3, 0, 4, 2, 7, 8, 9, 10, 5, 6,
    2, 0, 4, 1, 3, 8, 9, 10, 5, 6, 7,
    4, 2, 3, 0, 1, 9, 10, 5, 6, 7, 8,
    11, 8, 12, 6, 13, 10, 0, 2, 3, 4, 1,
    14, 9, 15, 7, 16, 2, 5, 4, 1, 3, 0,
    13, 10, 11, 8, 12, 4, 2, 6, 0, 1, 3,
    16, 5, 14, 9, 15, 0, 3, 1, 7, 2, 4,
    12, 6, 13, 10, 11, 3, 1, 0, 4, 8, 2,
    15, 7, 16, 5, 14, 1, 4, 3, 2, 0, 9]
private def pivots17 : Array (Fin 11) :=
  #[6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 0, 1, 1,
    1, 0, 0, 0]

theorem card17 : Realized 11 17 := by
  apply integerModel.certify
    (fun i x => alphabet17[(words17[i.val]! / 5 ^ x.val) % 5]!)
    (fun p => labels17[p.1.val * 11 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots17[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card17


private def alphabet18 : Array ℤ :=
  #[-375, -297, -7, 0, 1, 21,
    24, 40, 56, 72, 192, 297,
    304]
private def words18 : Array ℕ :=
  #[448044925318, 448102847026, 448855829230, 458644597882, 585898590358, 448040098522, 448040098678, 448040100706, 448040127070, 448040469802, 448040098510, 448040014074, 448040213793,
    448040098379, 448040118290, 448040094124, 448038985878, 448041584721]
private def labels18 : Array (Fin 18) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    3, 4, 1, 2, 0, 6, 7, 8, 9, 10, 5,
    1, 3, 0, 4, 2, 7, 8, 9, 10, 5, 6,
    2, 0, 4, 1, 3, 8, 9, 10, 5, 6, 7,
    4, 2, 3, 0, 1, 9, 10, 5, 6, 7, 8,
    9, 11, 12, 7, 13, 10, 0, 2, 3, 4, 1,
    6, 9, 7, 10, 8, 2, 5, 4, 1, 3, 0,
    5, 14, 9, 8, 15, 4, 2, 6, 0, 1, 3,
    8, 13, 10, 16, 17, 0, 3, 1, 7, 2, 4,
    14, 15, 13, 17, 16, 3, 1, 0, 4, 8, 2,
    15, 12, 11, 13, 14, 1, 4, 3, 2, 0, 9]
private def pivots18 : Array (Fin 11) :=
  #[6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 0, 1, 1,
    1, 0, 0, 1, 1]

theorem card18 : Realized 11 18 := by
  apply integerModel.certify
    (fun i x => alphabet18[(words18[i.val]! / 13 ^ x.val) % 13]!)
    (fun p => labels18[p.1.val * 11 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots18[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card18


private def alphabet19 : Array ℤ :=
  #[-9984, -609, -297, -87, -5, 0,
    1, 5, 12, 87, 297, 304,
    416, 2088, 2912, 2975, 10200]
private def words19 : Array ℕ :=
  #[10709991733704, 10710377934808, 10716943353576, 10828555472632, 12725961496584, 10709967596152, 10709967596424, 10709967601048, 10709967679656, 10709969015992, 10709967596136, 10709964790812, 10709967595897,
    10709977554786, 10709967597036, 10709961960935, 10709978930436, 10709968097346, 10709967345674]
private def labels19 : Array (Fin 19) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    3, 4, 1, 2, 0, 6, 7, 8, 9, 10, 5,
    1, 3, 0, 4, 2, 7, 8, 9, 10, 5, 6,
    2, 0, 4, 1, 3, 8, 9, 10, 5, 6, 7,
    4, 2, 3, 0, 1, 9, 10, 5, 6, 7, 8,
    11, 8, 12, 13, 14, 10, 0, 2, 3, 4, 1,
    6, 15, 13, 16, 8, 2, 5, 4, 1, 3, 0,
    17, 13, 11, 18, 10, 4, 2, 6, 0, 1, 3,
    18, 6, 10, 17, 9, 0, 3, 1, 7, 2, 4,
    13, 16, 14, 15, 12, 3, 1, 0, 4, 8, 2,
    10, 5, 8, 6, 7, 1, 4, 3, 2, 0, 9]
private def pivots19 : Array (Fin 11) :=
  #[6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 0, 3, 1,
    3, 1, 0, 0, 1, 1]

theorem card19 : Realized 11 19 := by
  apply integerModel.certify
    (fun i x => alphabet19[(words19[i.val]! / 17 ^ x.val) % 17]!)
    (fun p => labels19[p.1.val * 11 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots19[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card19

end OrderEleven
