module
public import Quantum.Pivots
/-! Explicit order-nine quantum Latin squares with kernel-checked coefficient arithmetic. -/
@[expose] public section
namespace NineSpectrum
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet11 : Array ℤ :=
  #[-3, 0, 1, 3, 4]
private def words11 : Array ℕ :=
  #[491406, 503906, 566406, 878906, 488906, 488306, 488286, 488282, 488406, 541406, 482031]
private def labels11 : Array (Fin 11) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    2, 3, 0, 1, 6, 8, 7, 4, 5,
    3, 0, 1, 2, 8, 7, 4, 5, 6,
    1, 2, 3, 0, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 9, 10, 3, 2,
    5, 8, 7, 4, 10, 6, 3, 2, 9,
    6, 7, 4, 8, 9, 2, 5, 10, 3,
    7, 4, 5, 6, 2, 3, 9, 8, 10,
    8, 5, 6, 7, 3, 10, 2, 9, 4]
private def pivots11 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 5, 5]

theorem card11 : Realized 9 11 := by
  apply integerModel.certify
    (fun i x => alphabet11[(words11[i.val]! / 5 ^ x.val) % 5]!)
    (fun p => labels11[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots11[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card11


private def alphabet12 : Array ℤ :=
  #[-4420, -2976, -2232, 0, 1, 744,
    817, 2451, 3268, 3315]
private def words12 : Array ℕ :=
  #[333433333, 334333333, 343333333, 433333333, 333343333, 333333433, 333333343, 333333334, 333334333, 336533333, 931833333, 32733333]
private def labels12 : Array (Fin 12) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    2, 3, 0, 1, 6, 8, 7, 4, 5,
    3, 0, 1, 2, 8, 7, 4, 5, 6,
    1, 2, 3, 0, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 9, 10, 11, 2,
    5, 8, 7, 4, 10, 6, 11, 2, 9,
    6, 7, 4, 8, 9, 2, 5, 10, 11,
    7, 4, 5, 6, 2, 11, 9, 8, 10,
    8, 5, 6, 7, 11, 10, 2, 9, 4]
private def pivots12 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 5, 5, 5]

theorem card12 : Realized 9 12 := by
  apply integerModel.certify
    (fun i x => alphabet12[(words12[i.val]! / 10 ^ x.val) % 10]!)
    (fun p => labels12[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots12[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card12


private def alphabet13 : Array ℤ :=
  #[-552500, -100019, -4420, -2232, 0, 1,
    2451, 52392, 69615, 79560, 92820, 231624,
    308832, 336468, 414375, 448624]
private def words13 : Array ℕ :=
  #[18326242372, 18341971012, 18593629252, 22620161092, 18325259332, 18325194052, 18325193812, 18325193797, 18325197892, 46925104196, 39752844356, 9720579140, 34558198852]
private def labels13 : Array (Fin 13) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    2, 3, 0, 1, 6, 8, 7, 4, 5,
    3, 0, 1, 2, 8, 7, 4, 5, 6,
    1, 2, 3, 0, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 9, 10, 11, 12,
    5, 8, 7, 4, 10, 6, 11, 12, 9,
    6, 7, 4, 8, 9, 12, 5, 10, 11,
    7, 4, 5, 6, 12, 11, 9, 8, 10,
    8, 5, 6, 7, 11, 10, 12, 9, 4]
private def pivots13 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 5, 5, 5, 5]

theorem card13 : Realized 9 13 := by
  apply integerModel.certify
    (fun i x => alphabet13[(words13[i.val]! / 16 ^ x.val) % 16]!)
    (fun p => labels13[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots13[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card13


private def alphabet14 : Array ℤ :=
  #[-4420, -2976, -2232, -8, 0, 1,
    8, 15, 744, 817, 2451, 3268,
    3315]
private def words14 : Array ℕ :=
  #[3535204417, 3539659933, 3597581641, 4350563845, 3534861685, 3534833293, 3534833137, 3534833125, 3534835321, 2733582830, 5991678905, 3560452341, 10048797516,
    264484380]
private def labels14 : Array (Fin 14) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    2, 3, 0, 1, 6, 8, 7, 4, 5,
    9, 0, 10, 2, 8, 7, 4, 5, 6,
    10, 2, 9, 0, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 11, 12, 13, 2,
    5, 8, 7, 4, 12, 6, 13, 2, 11,
    6, 7, 4, 8, 11, 2, 5, 12, 13,
    7, 4, 5, 6, 2, 13, 11, 8, 12,
    8, 5, 6, 7, 13, 12, 2, 11, 4]
private def pivots14 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 6, 5, 5,
    5]

theorem card14 : Realized 9 14 := by
  apply integerModel.certify
    (fun i x => alphabet14[(words14[i.val]! / 13 ^ x.val) % 13]!)
    (fun p => labels14[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots14[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card14


private def alphabet15 : Array ℤ :=
  #[-225, -120, -45, -32, -24, 0,
    1, 8, 15, 24, 45, 60,
    64, 120, 225]
private def words15 : Array ℕ :=
  #[13730530580, 13741161830, 13900630580, 16292661830, 13729821830, 13729771430, 13729771220, 13729771206, 13729774580, 21441224330, 14243868080, 8505271205, 23609999330,
    35856439955, 2241946205]
private def labels15 : Array (Fin 15) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    2, 3, 0, 1, 6, 8, 7, 4, 5,
    3, 0, 1, 2, 8, 7, 4, 5, 6,
    1, 2, 3, 0, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 9, 10, 11, 12,
    5, 8, 7, 4, 11, 6, 12, 13, 14,
    6, 7, 4, 8, 14, 11, 5, 12, 13,
    7, 4, 5, 6, 12, 10, 9, 8, 11,
    8, 5, 6, 7, 13, 12, 11, 14, 4]
private def pivots15 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 5, 5, 5,
    5, 5]

theorem card15 : Realized 9 15 := by
  apply integerModel.certify
    (fun i x => alphabet15[(words15[i.val]! / 15 ^ x.val) % 15]!)
    (fun p => labels15[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots15[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card15


private def alphabet16 : Array ℤ :=
  #[-225, -120, -45, -32, -24, -8,
    0, 1, 8, 15, 24, 45,
    60, 64, 120, 225]
private def words16 : Array ℕ :=
  #[27488839270, 27504567910, 27756226150, 31782757990, 27487856230, 27487790950, 27487790710, 27487790695, 27487794790, 23243155046, 40406247014, 28295194214, 14171924070,
    43801536102, 64389277286, 3788924518]
private def labels16 : Array (Fin 16) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    2, 3, 0, 1, 6, 8, 7, 4, 5,
    9, 0, 10, 2, 8, 7, 4, 5, 6,
    10, 2, 9, 0, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 10, 11, 12, 13,
    5, 8, 7, 4, 12, 6, 13, 14, 15,
    6, 7, 4, 8, 15, 12, 5, 13, 14,
    7, 4, 5, 6, 13, 11, 10, 8, 12,
    8, 5, 6, 7, 14, 13, 12, 15, 4]
private def pivots16 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 6, 5, 5,
    5, 5, 5]

theorem card16 : Realized 9 16 := by
  apply integerModel.certify
    (fun i x => alphabet16[(words16[i.val]! / 16 ^ x.val) % 16]!)
    (fun p => labels16[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots16[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card16


private def alphabet17 : Array ℤ :=
  #[-225, -120, -45, -32, -24, -7,
    0, 1, 7, 8, 15, 24,
    45, 60, 64, 120, 225]
private def words17 : Array ℕ :=
  #[44471873543, 44494591255, 44880792359, 51446211127, 44470537207, 44470453975, 44470453703, 44470453687, 44470458599, 44067214298, 46524986765, 72445896157, 46116067949,
    22899986142, 78031613595, 111561536650, 6199628108]
private def labels17 : Array (Fin 17) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    1, 9, 3, 10, 6, 8, 7, 4, 5,
    3, 10, 1, 9, 8, 7, 4, 5, 6,
    2, 3, 0, 1, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 11, 12, 13, 14,
    5, 8, 7, 4, 13, 6, 14, 15, 16,
    6, 7, 4, 8, 16, 13, 5, 14, 15,
    7, 4, 5, 6, 14, 12, 11, 8, 13,
    8, 5, 6, 7, 15, 14, 13, 16, 4]
private def pivots17 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 5, 5, 6, 5,
    5, 5, 5, 5]

theorem card17 : Realized 9 17 := by
  apply integerModel.certify
    (fun i x => alphabet17[(words17[i.val]! / 17 ^ x.val) % 17]!)
    (fun p => labels17[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots17[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card17


private def alphabet18 : Array ℤ :=
  #[-225, -120, -45, -32, -24, -8,
    -3, 0, 1, 3, 4, 8,
    15, 24, 45, 60, 64, 120,
    225]
private def words18 : Array ℕ :=
  #[125492136346, 125536706128, 126383531986, 142473223288, 125489790568, 125489660608, 125489660266, 125489660248, 125489667106, 91757763570, 128176227662, 210595658976, 124603216805,
    129968923338, 55267492607, 223600130924, 305606053705, 15283445955]
private def labels18 : Array (Fin 18) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    2, 3, 0, 1, 6, 8, 7, 4, 5,
    9, 10, 11, 12, 8, 7, 4, 5, 6,
    11, 12, 9, 10, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 11, 13, 14, 15,
    5, 8, 7, 4, 14, 6, 15, 16, 17,
    6, 7, 4, 8, 17, 14, 5, 15, 16,
    7, 4, 5, 6, 15, 13, 11, 8, 14,
    8, 5, 6, 7, 16, 15, 14, 17, 4]
private def pivots18 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 5, 6, 5,
    5, 5, 5, 5, 5]

theorem card18 : Realized 9 18 := by
  apply integerModel.certify
    (fun i x => alphabet18[(words18[i.val]! / 19 ^ x.val) % 19]!)
    (fun p => labels18[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots18[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card18


private def alphabet19 : Array ℤ :=
  #[-744, -225, -171, -120, -45, -32,
    -24, 0, 1, 8, 15, 24,
    45, 60, 64, 120, 140, 171,
    225, 744, 817]
private def words19 : Array ℕ :=
  #[278002100404, 278083782424, 279799104844, 315820875664, 277998210784, 277998016744, 277998016324, 277998016304, 277998025564, 619261411762, 301461176548, 89655614587, 265443489829,
    391638126628, 283409450128, 201086226271, 425454482908, 601025900797, 65155092688]
private def labels19 : Array (Fin 19) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    2, 3, 0, 1, 6, 8, 7, 4, 5,
    9, 10, 11, 12, 8, 7, 4, 5, 6,
    11, 12, 9, 10, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 13, 14, 15, 16,
    5, 8, 7, 4, 15, 6, 16, 17, 18,
    6, 7, 4, 8, 18, 15, 5, 16, 17,
    7, 4, 5, 6, 16, 14, 13, 8, 15,
    8, 5, 6, 7, 17, 16, 15, 18, 4]
private def pivots19 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 5, 6, 5,
    6, 5, 5, 5, 5, 5]

theorem card19 : Realized 9 19 := by
  apply integerModel.certify
    (fun i x => alphabet19[(words19[i.val]! / 21 ^ x.val) % 21]!)
    (fun p => labels19[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots19[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card19

end NineSpectrum
