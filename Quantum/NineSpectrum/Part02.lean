module
public import Quantum.Pivots
/-! Explicit order-nine quantum Latin squares with kernel-checked coefficient arithmetic. -/
@[expose] public section
namespace NineSpectrum
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet20 : Array ℤ :=
  #[-225, -120, -45, -32, -24, -8,
    -4, -3, 0, 1, 3, 4,
    8, 15, 24, 45, 60, 64,
    120, 225]
private def words20 : Array ℕ :=
  #[215582147368, 215642947368, 216858947368, 241178947368, 215579107368, 215578947768, 215578947388, 215578947369, 215578955368, 139098947368, 219425347368, 343834947368, 214308547368,
    215578948228, 215578946608, 221991747368, 82993347368, 362420547368, 486266947368, 23159747368]
private def labels20 : Array (Fin 20) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    2, 3, 0, 1, 6, 8, 7, 4, 5,
    9, 10, 11, 12, 8, 7, 4, 5, 6,
    11, 12, 9, 10, 5, 4, 8, 6, 7,
    4, 13, 8, 14, 7, 11, 15, 16, 17,
    5, 8, 7, 4, 16, 6, 17, 18, 19,
    6, 7, 4, 8, 19, 16, 5, 17, 18,
    7, 4, 14, 13, 17, 15, 11, 8, 16,
    8, 14, 13, 7, 18, 17, 16, 19, 4]
private def pivots20 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 5, 6, 5,
    1, 1, 5, 5, 5, 5, 5]

theorem card20 : Realized 9 20 := by
  apply integerModel.certify
    (fun i x => alphabet20[(words20[i.val]! / 20 ^ x.val) % 20]!)
    (fun p => labels20[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots20[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card20


private def alphabet21 : Array ℤ :=
  #[-4, -3, -2, -1, 0, 1,
    2, 3, 4]
private def words21 : Array ℕ :=
  #[193769293, 194241685, 198493213, 236756965, 193716805, 193710325, 193710253, 193710245, 193710973, 332947786, 265513828, 152375944, 197607478,
    114525535, 246559099, 20519527, 175227907, 227722468, 102892882, 236343622, 199615144]
private def labels21 : Array (Fin 21) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    9, 10, 11, 12, 6, 8, 7, 4, 5,
    13, 14, 15, 16, 8, 7, 4, 5, 6,
    17, 18, 19, 20, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 1, 0, 3, 2,
    5, 8, 7, 4, 0, 6, 3, 2, 1,
    6, 7, 4, 8, 1, 2, 5, 0, 3,
    7, 4, 5, 6, 2, 3, 1, 8, 0,
    8, 5, 6, 7, 3, 0, 2, 1, 4]
private def pivots21 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 5, 5, 5,
    6, 5, 5, 5, 6, 5, 5, 5]

theorem card21 : Realized 9 21 := by
  apply integerModel.certify
    (fun i x => alphabet21[(words21[i.val]! / 9 ^ x.val) % 9]!)
    (fun p => labels21[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots21[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card21


private def alphabet22 : Array ℤ :=
  #[-225, -120, -45, -36, -32, -24,
    -8, -4, -3, 0, 1, 3,
    4, 8, 15, 24, 36, 45,
    60, 64, 77, 120, 225]
private def words22 : Array ℕ :=
  #[736841616032, 736983215578, 740240005136, 815146164970, 736835459530, 736835180218, 736835179712, 736835179690, 736835191856, 736835180816, 736835178677, 502642403291, 747062528716,
    1128982249650, 733449663271, 736835176768, 736835185669, 753885052296, 333044765241, 1188698640004, 1722387328878, 71774293842]
private def labels22 : Array (Fin 22) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    2, 3, 0, 1, 9, 8, 7, 4, 10,
    11, 12, 13, 14, 8, 7, 4, 10, 9,
    13, 14, 11, 12, 10, 4, 8, 9, 7,
    4, 15, 8, 16, 7, 13, 17, 18, 19,
    5, 8, 7, 4, 18, 6, 19, 20, 21,
    6, 7, 4, 8, 21, 18, 5, 19, 20,
    7, 4, 16, 15, 19, 17, 13, 8, 18,
    8, 16, 15, 7, 20, 19, 18, 21, 4]
private def pivots22 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 1, 1, 6, 5,
    6, 5, 1, 1, 5, 5, 5, 5, 5]

theorem card22 : Realized 9 22 := by
  apply integerModel.certify
    (fun i x => alphabet22[(words22[i.val]! / 23 ^ x.val) % 23]!)
    (fun p => labels22[p.1.val * 9 + p.2.val]!)
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
  #[193769293, 194241685, 198493213, 236756965, 193716805, 193710325, 193710253, 193710245, 193710973, 332947786, 265513828, 152375944, 197607478,
    114525535, 246559099, 20519527, 175227907, 227722468, 102892882, 236343622, 199615144, 196013155, 192352117]
private def labels23 : Array (Fin 23) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    9, 10, 11, 12, 6, 8, 7, 4, 5,
    13, 14, 15, 16, 8, 7, 4, 5, 6,
    17, 18, 19, 20, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 21, 22, 3, 2,
    5, 8, 7, 4, 22, 6, 3, 2, 21,
    6, 7, 4, 8, 21, 2, 5, 22, 3,
    7, 4, 5, 6, 2, 3, 21, 8, 22,
    8, 5, 6, 7, 3, 22, 2, 21, 4]
private def pivots23 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 5, 5, 5,
    6, 5, 5, 5, 6, 5, 5, 5, 5, 5]

theorem card23 : Realized 9 23 := by
  apply integerModel.certify
    (fun i x => alphabet23[(words23[i.val]! / 9 ^ x.val) % 9]!)
    (fun p => labels23[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots23[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card23


private def alphabet24 : Array ℤ :=
  #[-4420, -2976, -2232, -4, -3, -2,
    -1, 0, 1, 2, 3, 4,
    744, 817, 2451, 3268, 3315]
private def words24 : Array ℕ :=
  #[51883615824, 51906333536, 52292534640, 58857953408, 51882279488, 51882196256, 51882195984, 51882195968, 51882200880, 73654283205, 64604114687, 44981690947, 52248519073,
    38437570034, 59684310182, 23932310922, 50267818558, 58061413631, 37521762269, 58836655553, 52342229635, 52034120666, 114530546378, 2941145034]
private def labels24 : Array (Fin 24) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    9, 10, 11, 12, 6, 8, 7, 4, 5,
    13, 14, 15, 16, 8, 7, 4, 5, 6,
    17, 18, 19, 20, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 21, 22, 23, 2,
    5, 8, 7, 4, 22, 6, 23, 2, 21,
    6, 7, 4, 8, 21, 2, 5, 22, 23,
    7, 4, 5, 6, 2, 23, 21, 8, 22,
    8, 5, 6, 7, 23, 22, 2, 21, 4]
private def pivots24 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 5, 5, 5,
    6, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5]

theorem card24 : Realized 9 24 := by
  apply integerModel.certify
    (fun i x => alphabet24[(words24[i.val]! / 17 ^ x.val) % 17]!)
    (fun p => labels24[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots24[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card24


private def alphabet25 : Array ℤ :=
  #[-552500, -100019, -4420, -2232, -4, -3,
    -2, -1, 0, 1, 2, 3,
    4, 2451, 52392, 69615, 79560, 92820,
    231624, 308832, 336468, 414375, 448624]
private def words25 : Array ℕ :=
  #[654971040511, 655112640057, 658369429615, 733275589449, 654964884009, 654964604697, 654964604191, 654964604169, 654964616335, 896855246794, 801378534732, 577110599240, 658092666866,
    502339602609, 740110985715, 341431027609, 641506210955, 726613974444, 494944244502, 733140426246, 658671937736, 1405744706089, 1280454853251, 184390694752, 1177460492565]
private def labels25 : Array (Fin 25) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    9, 10, 11, 12, 6, 8, 7, 4, 5,
    13, 14, 15, 16, 8, 7, 4, 5, 6,
    17, 18, 19, 20, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 21, 22, 23, 24,
    5, 8, 7, 4, 22, 6, 23, 24, 21,
    6, 7, 4, 8, 21, 24, 5, 22, 23,
    7, 4, 5, 6, 24, 23, 21, 8, 22,
    8, 5, 6, 7, 23, 22, 24, 21, 4]
private def pivots25 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 5, 5, 5,
    6, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5, 5]

theorem card25 : Realized 9 25 := by
  apply integerModel.certify
    (fun i x => alphabet25[(words25[i.val]! / 23 ^ x.val) % 23]!)
    (fun p => labels25[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots25[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card25


private def alphabet26 : Array ℤ :=
  #[-20, -16, -15, -11, -10, -7,
    -6, -5, -4, -1, 0, 1,
    2, 3, 4, 5, 6, 7,
    10, 11, 12, 16, 17, 24]
private def words26 : Array ℕ :=
  #[1148253655930, 1149217133434, 1153198445434, 1258687288186, 1148612305786, 1148611974586, 1148611974034, 1148611974011, 1148611987834, 241095791482, 1992164397946, 1701329556346, 1170875470714,
    2017453691770, 1734040015738, 48312701818, 1101425464186, 855682962298, 474042356602, 1258512110458, 1144415671162, 1209573823354, 1128163955578, 1148619936634, 1163135800186, 1140012340090]
private def labels26 : Array (Fin 26) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    9, 10, 11, 12, 6, 8, 7, 4, 5,
    13, 14, 15, 16, 8, 7, 4, 5, 6,
    17, 18, 19, 20, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 21, 3, 22, 23,
    5, 8, 7, 4, 24, 6, 25, 23, 3,
    6, 7, 4, 8, 23, 3, 5, 21, 22,
    7, 4, 5, 6, 3, 22, 23, 8, 21,
    8, 5, 6, 7, 25, 23, 24, 3, 4]
private def pivots26 : Array (Fin 9) :=
  #[5, 5, 7, 8, 4, 2, 1, 0, 3, 5, 5, 5, 5,
    5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 5, 6, 6]

theorem card26 : Realized 9 26 := by
  apply integerModel.certify
    (fun i x => alphabet26[(words26[i.val]! / 24 ^ x.val) % 24]!)
    (fun p => labels26[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots26[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card26


private def alphabet27 : Array ℤ :=
  #[-225, -120, -45, -32, -24, -4,
    -3, -2, -1, 0, 1, 2,
    3, 4, 8, 15, 24, 45,
    60, 64, 120, 225]
private def words27 : Array ℕ :=
  #[517406246971, 517514473243, 519895451227, 572276966875, 517401327595, 517401093823, 517401093361, 517401093340, 517401103987, 687130809627, 619674920379, 462875666779, 519684152315,
    410597223771, 577286297179, 297675993019, 507547348955, 567401631003, 405160142011, 572173894235, 520127364667, 847223234075, 532393008827, 176735710875, 885818784123, 1152158485883,
    50100665371]
private def labels27 : Array (Fin 27) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    9, 10, 11, 12, 6, 8, 7, 4, 5,
    13, 14, 15, 16, 8, 7, 4, 5, 6,
    17, 18, 19, 20, 5, 4, 8, 6, 7,
    4, 6, 8, 5, 7, 21, 22, 23, 24,
    5, 8, 7, 4, 23, 6, 24, 25, 26,
    6, 7, 4, 8, 26, 23, 5, 24, 25,
    7, 4, 5, 6, 24, 22, 21, 8, 23,
    8, 5, 6, 7, 25, 24, 23, 26, 4]
private def pivots27 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 5, 5, 5,
    6, 5, 5, 5, 6, 5, 5, 5, 6, 5, 5, 5, 5,
    5]

theorem card27 : Realized 9 27 := by
  apply integerModel.certify
    (fun i x => alphabet27[(words27[i.val]! / 22 ^ x.val) % 22]!)
    (fun p => labels27[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots27[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card27


private def alphabet28 : Array ℤ :=
  #[-20, -16, -15, -11, -10, -7,
    -6, -5, -4, -1, 0, 1,
    2, 3, 4, 5, 6, 7,
    10, 11, 12, 16, 17, 24]
private def words28 : Array ℕ :=
  #[1148253655930, 1149217133434, 1153198445434, 1258687288186, 1148612305786, 1148611974586, 1148611974034, 1148611974011, 1148611987834, 241095791482, 1992164397946, 1701329556346, 1170875470714,
    2017453691770, 1734040015738, 48312701818, 1101425464186, 855682962298, 474042356602, 1258512110458, 1144415671162, 1148611975834, 1148611972930, 1209573823354, 1128163955578, 1148619936634,
    1163135800186, 1140012340090]
private def labels28 : Array (Fin 28) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    9, 10, 11, 12, 6, 8, 7, 4, 5,
    13, 14, 15, 16, 8, 7, 4, 5, 6,
    17, 18, 19, 20, 5, 4, 8, 6, 7,
    4, 21, 8, 22, 7, 23, 3, 24, 25,
    5, 8, 7, 4, 26, 6, 27, 25, 3,
    6, 7, 4, 8, 25, 3, 5, 23, 24,
    7, 4, 22, 21, 3, 24, 25, 8, 23,
    8, 22, 21, 7, 27, 25, 26, 3, 4]
private def pivots28 : Array (Fin 9) :=
  #[5, 5, 7, 8, 4, 2, 1, 0, 3, 5, 5, 5, 5,
    5, 5, 5, 5, 5, 5, 5, 5, 1, 1, 6, 6, 5,
    6, 6]

theorem card28 : Realized 9 28 := by
  apply integerModel.certify
    (fun i x => alphabet28[(words28[i.val]! / 24 ^ x.val) % 24]!)
    (fun p => labels28[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots28[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card28


private def alphabet29 : Array ℤ :=
  #[-225, -120, -45, -32, -24, -4,
    -3, -2, -1, 0, 1, 2,
    3, 4, 8, 15, 24, 45,
    60, 64, 120, 225]
private def words29 : Array ℕ :=
  #[517406246971, 517514473243, 519895451227, 572276966875, 517401327595, 517401093823, 517401093361, 517401093340, 517401103987, 687130809627, 619674920379, 462875666779, 519684152315,
    410597223771, 577286297179, 297675993019, 507547348955, 567401631003, 405160142011, 572173894235, 520127364667, 517401094879, 517401091469, 847223234075, 532393008827, 176735710875,
    885818784123, 1152158485883, 50100665371]
private def labels29 : Array (Fin 29) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8,
    9, 10, 11, 12, 6, 8, 7, 4, 5,
    13, 14, 15, 16, 8, 7, 4, 5, 6,
    17, 18, 19, 20, 5, 4, 8, 6, 7,
    4, 21, 8, 22, 7, 23, 24, 25, 26,
    5, 8, 7, 4, 25, 6, 26, 27, 28,
    6, 7, 4, 8, 28, 25, 5, 26, 27,
    7, 4, 22, 21, 26, 24, 23, 8, 25,
    8, 22, 21, 7, 27, 26, 25, 28, 4]
private def pivots29 : Array (Fin 9) :=
  #[5, 6, 7, 8, 4, 2, 1, 0, 3, 6, 5, 5, 5,
    6, 5, 5, 5, 6, 5, 5, 5, 1, 1, 6, 5, 5,
    5, 5, 5]

theorem card29 : Realized 9 29 := by
  apply integerModel.certify
    (fun i x => alphabet29[(words29[i.val]! / 22 ^ x.val) % 22]!)
    (fun p => labels29[p.1.val * 9 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply integerModel.distinct_of_pivots (fun i => pivots29[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card29

end NineSpectrum
