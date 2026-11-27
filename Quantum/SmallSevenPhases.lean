module
public import Quantum.Pivots
public import Quantum.Biquadratic
/-! Explicit projective-ray certificates of order seven. -/
@[expose] public section
namespace SmallSeven
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet41 : Array IQ := #[(-6, -2), (-6, 2), (-3, -1), (-3, 1), (1, -3), (1, 0), (1, 3),
    (4, 0), (8, 0)]
private def words41 : Array ℕ := #[2989355, 1497967, 3885847, 4318235, 1206079, 1030931, 622907, 3913135, 1291696, 4151968, 4543469, 1524607, 600065,
    775331, 2055967, 4158448, 1764088, 3860647, 2627981, 2211947, 472940, 3718394, 4382, 3241196, 3918967, 1789927,
    3944815, 2022847, 820979, 2192795, 2374451, 4290956, 4650218, 355004, 2055319, 45692, 3189212, 393740, 1492135,
    3548780, 3886495]
private def slots41 : Array (Fin 41) := #[0, 1, 2, 3, 4, 5, 6,
    7, 8, 9, 10, 11, 12, 13,
    14, 15, 16, 12, 17, 18, 19,
    20, 21, 22, 8, 23, 15, 24,
    25, 26, 27, 28, 0, 29, 30,
    31, 22, 32, 9, 33, 16, 34,
    35, 36, 37, 38, 39, 40, 0]
private def pivots41 : Array (Fin 7) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0]

theorem card41 : Realized 7 41 := by
  apply (imaginaryModel 7 (by decide)).certify
    (fun i x => alphabet41[(words41[i.val]! / 9 ^ x.val) % 9]!)
    (fun p => slots41[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 7 (by decide)).distinct_of_pivots (fun i => pivots41[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card41


private def alphabet43 : Array IQ :=
  #[(-2, 0), (-1, -1), (-1, 1), (1, -1), (1, 0), (1, 1),
    (2, 0)]
private def words43 : Array ℕ :=
  #[549028, 235983, 16148, 219435, 735153, 388688, 343412, 118677, 689114, 250305, 206247, 65582, 711794,
    15476, 453830, 590036, 96200, 286999, 361087, 336650, 132908, 354115, 255464, 636621, 225021, 747452,
    292634, 57889, 156596, 375367, 272467, 607221, 98895, 203552, 384866, 624693, 21951, 230607, 710121,
    600746, 339590, 141063, 36357]
private def labels43 : Array (Fin 43) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 0, 8, 9, 10, 11, 12,
    13, 14, 0, 15, 16, 17, 18,
    19, 20, 21, 0, 22, 23, 24,
    25, 26, 27, 28, 0, 29, 30,
    31, 32, 33, 34, 35, 0, 36,
    37, 38, 39, 40, 41, 42, 0]
private def pivots43 : Array (Fin 7) :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0]

theorem card43 : Realized 7 43 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet43[(words43[i.val]! / 7 ^ x.val) % 7]!)
    (fun p => labels43[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots43[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card43


private def alphabet44 : Array IQ :=
  #[(-2, 0), (-1, -1), (-1, 1), (1, -1), (1, 0), (1, 1),
    (2, 0)]
private def words44 : Array ℕ :=
  #[549028, 118677, 101912, 250214, 761858, 592815, 216201, 351231, 604407, 808961, 158864, 466591, 253245,
    15476, 690843, 706551, 468299, 40389, 222095, 620318, 336650, 722525, 118397, 295007, 12641, 791937,
    747452, 173270, 802423, 639687, 126216, 607221, 452185, 150065, 84671, 596469, 333465, 403437, 230607,
    238839, 692348, 719907, 169434, 360219]
private def labels44 : Array (Fin 44) :=
  #[0, 1, 2, 3, 4, 5, 6,
    1, 7, 8, 9, 10, 11, 12,
    13, 14, 15, 16, 17, 18, 19,
    20, 21, 16, 22, 23, 24, 25,
    26, 27, 17, 23, 28, 29, 30,
    31, 32, 33, 34, 35, 36, 37,
    38, 39, 40, 41, 42, 43, 36]
private def pivots44 : Array (Fin 7) :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0]

theorem card44 : Realized 7 44 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet44[(words44[i.val]! / 7 ^ x.val) % 7]!)
    (fun p => labels44[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots44[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card44


private def alphabet45 : Array IQ :=
  #[(-2, 0), (-1, -1), (-1, 0), (-1, 1), (1, -1), (1, 0),
    (1, 1), (2, 0)]
private def words45 : Array ℕ :=
  #[1497965, 787455, 232487, 292751, 2036423, 1064543, 946271, 264191, 1601575, 1016719, 323271, 247391, 1935455,
    30775, 1278007, 1387373, 1834087, 37135, 1030535, 1177479, 1016607, 292639, 1308919, 1009575, 1589775, 396303,
    1951303, 933447, 111007, 410423, 1205991, 1001703, 1609423, 225999, 326919, 1246751, 1729143, 2052095, 599405,
    516303, 1842383, 1807111, 813087, 478327, 1994751]
private def labels45 : Array (Fin 45) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 0, 8, 9, 10, 11, 12,
    13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 15, 23, 24, 25,
    26, 27, 28, 29, 15, 30, 31,
    32, 33, 34, 35, 36, 37, 38,
    39, 40, 41, 42, 43, 38, 44]
private def pivots45 : Array (Fin 7) :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0]

theorem card45 : Realized 7 45 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet45[(words45[i.val]! / 8 ^ x.val) % 8]!)
    (fun p => labels45[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots45[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card45


private def alphabet46 : Array IQ :=
  #[(-2, 0), (-1, -1), (-1, 1), (1, -1), (1, 0), (1, 1),
    (2, 0)]
private def words46 : Array ℕ :=
  #[549028, 36357, 52520, 727670, 284402, 230607, 710121, 118677, 652042, 636992, 210083, 758085, 238839,
    15476, 759443, 740851, 89627, 418375, 601110, 105475, 336650, 400448, 418221, 261085, 151290, 811145,
    248625, 747452, 17891, 89781, 819797, 261169, 167033, 756650, 607221, 134287, 629355, 102206, 372224,
    686069, 631231, 641241, 136807, 752534, 343069, 125264]
private def labels46 : Array (Fin 46) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 8, 9, 10, 11, 12, 5,
    13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31, 32, 33,
    34, 5, 35, 36, 37, 38, 39,
    5, 40, 41, 42, 43, 44, 45]
private def pivots46 : Array (Fin 7) :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0]

theorem card46 : Realized 7 46 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet46[(words46[i.val]! / 7 ^ x.val) % 7]!)
    (fun p => labels46[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots46[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card46


private def alphabet47 : Array IQ :=
  #[(-2, 0), (-1, -1), (-1, 1), (1, -1), (1, 0), (1, 1),
    (2, 0)]
private def words47 : Array ℕ :=
  #[549028, 17835, 15476, 740018, 344084, 203853, 734817, 118677, 687371, 690843, 184701, 711094, 267308,
    205225, 791685, 821799, 50525, 362123, 606255, 96900, 336650, 386385, 353051, 284066, 225378, 804971,
    256514, 747452, 106042, 59597, 729588, 271802, 123472, 822506, 607221, 166466, 202887, 704129, 22630,
    419901, 624329, 230607, 608593, 601110, 155672, 321803, 141385]
private def labels47 : Array (Fin 47) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 8, 9, 10, 11, 12, 13,
    2, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26,
    27, 28, 29, 30, 31, 32, 33,
    34, 35, 36, 37, 38, 39, 40,
    41, 42, 43, 44, 33, 45, 46]
private def pivots47 : Array (Fin 7) :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0]

theorem card47 : Realized 7 47 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet47[(words47[i.val]! / 7 ^ x.val) % 7]!)
    (fun p => labels47[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots47[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card47


private def alphabet48 : Array IQ :=
  #[(-2, 0), (-1, -1), (-1, 1), (1, -1), (1, 0), (1, 1),
    (2, 0)]
private def words48 : Array ℕ :=
  #[549028, 19011, 706082, 49118, 459038, 87429, 620157, 118677, 687518, 234114, 640450, 9365, 617707,
    437338, 15476, 791146, 101646, 771315, 240260, 726844, 218126, 336650, 384768, 251474, 386574, 697248,
    451240, 747452, 106630, 762159, 25850, 400966, 433, 696919, 607221, 167789, 686958, 219862, 730337,
    180879, 269765, 230607, 607515, 122380, 634892, 102647, 680630, 382955]
private def labels48 : Array (Fin 48) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 8, 9, 10, 11, 12, 13,
    14, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 24, 25, 26, 1,
    27, 28, 29, 30, 31, 32, 33,
    34, 35, 36, 37, 38, 39, 40,
    41, 42, 43, 44, 45, 46, 47]
private def pivots48 : Array (Fin 7) :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem card48 : Realized 7 48 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet48[(words48[i.val]! / 7 ^ x.val) % 7]!)
    (fun p => labels48[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots48[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card48


private def alphabet49 : Array IQ :=
  #[(-2, 0), (-1, -1), (-1, 1), (1, -1), (1, 0), (1, 1),
    (2, 0)]
private def words49 : Array ℕ :=
  #[549028, 17835, 706964, 48530, 459332, 88605, 619569, 118677, 687371, 234653, 640891, 7601, 617854,
    438122, 15476, 791685, 101499, 770825, 242073, 726305, 216950, 336650, 386385, 249808, 387309, 698375,
    449623, 18815, 747452, 106042, 763090, 26095, 399055, 1021, 697654, 607221, 166466, 687889, 219127,
    730925, 182202, 268981, 230607, 608593, 120910, 635872, 102206, 679552, 383886]
private def labels49 : Array (Fin 49) :=
  #[0, 1, 2, 3, 4, 5, 6,
    7, 8, 9, 10, 11, 12, 13,
    14, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 24, 25, 26, 27,
    28, 29, 30, 31, 32, 33, 34,
    35, 36, 37, 38, 39, 40, 41,
    42, 43, 44, 45, 46, 47, 48]
private def pivots49 : Array (Fin 7) :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem card49 : Realized 7 49 := by
  apply (imaginaryModel 3 (by decide)).certify
    (fun i x => alphabet49[(words49[i.val]! / 7 ^ x.val) % 7]!)
    (fun p => labels49[p.1.val * 7 + p.2.val]!)
  · decide +kernel
  · decide +kernel
  · apply (imaginaryModel 3 (by decide)).distinct_of_pivots (fun i => pivots49[i.val]!)
    decide +kernel
  all_goals decide +kernel

#print axioms card49

end SmallSeven
