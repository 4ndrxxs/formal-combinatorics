module
public import Quantum.DiagonalBlocks
public import Quantum.PartialCertificates

@[expose] public section
namespace SmallEven.B8_19
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-23400, -18720, -16380, -10920, -8580, -7800,
  -7020, -6825, -5460, -3900, -3640, -2100,
  -1950, -1040, 0, 520, 546, 1170,
  1560, 1755, 1820, 1950, 2730, 3120,
  3510, 3900, 4200, 4680, 5460, 6240,
  6552, 7800, 8190, 27300]
private def words : Array ℕ := #[116566, 217016, 249860, 270430, 294590, 318404, 385010, 397474,
  566944, 567406, 583114, 732422, 888774, 905006, 924080, 998166,
  1035586, 1117186, 1218234]
private def codes : Array ℕ := #[1777666460743006470, 3174300331470561540, 3301259647372693110, 3301284064861813680, 3333009243917752581, 3555170142100766280,
  3809153885122500720, 3851430251350600100, 4443983024415594660, 4443983024713710660, 4443999302145426660, 4697926074230690925,
  4888378614051233210, 4951787735545660620, 4951860984882747000, 5078823014534842040, 5127653938552352760, 5332763351270742660,
  5510600805589082112]
private def pivots : Array (Fin 4) := #[1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 2, 0,
  1, 0, 0, 0, 1, 3, 1]
private def positions : Array ℕ := #[39, 44, 53, 61, 54, 63, 47, 37, 38, 24, 27, 55,
  36, 52, 60, 45, 62, 25, 46]
private def slots : Array (Fin 19) := #[8, 9, 10, 17, 0, 0, 0, 0,
  10, 8, 17, 9, 0, 0, 0, 0,
  17, 10, 9, 8, 0, 0, 0, 0,
  9, 17, 8, 10, 0, 0, 0, 0,
  0, 0, 0, 0, 12, 7, 8, 0,
  0, 0, 0, 0, 1, 15, 18, 6,
  0, 0, 0, 0, 13, 2, 4, 11,
  0, 0, 0, 0, 14, 3, 16, 5]
private def rep (i : Fin 19) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 34 ^ x.val) % 34]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 27300).toNat) * 54601 ^ x.val
private def label (p : Cell 8) : Fin 19 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 19) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 19 (evenMask 4)) := by
  apply integerModel.partialArray (evenMask 4) rep label (fun i => pivots[i.val]!) 5460 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 4) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B8_19

namespace SmallEven.B8_23
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-23400, -18720, -16380, -10920, -8580, -7800,
  -7280, -7020, -6825, -5460, -4095, -3900,
  -3640, -2100, -1950, -1040, 0, 520,
  546, 1170, 1560, 1755, 1820, 1950,
  2730, 3120, 3510, 3900, 4095, 4200,
  4680, 5460, 6240, 6552, 7280, 7800,
  8190, 27300]
private def words : Array ℕ := #[162922, 302815, 352975, 404503, 431673, 466162, 498819, 646981,
  663990, 893586, 901695, 902250, 923340, 928242, 1131481, 1349890,
  1373047, 1399799, 1503881, 1560159, 1611254, 1724760, 1865398]
private def codes : Array ℕ := #[1777666460743006470, 3174300331470561540, 3258942588608723380, 3301259647372693110, 3301284064861813680, 3333009243917752581,
  3555170142100766280, 3809153885122500720, 3851430251350600100, 4443970816416332565, 4443983024415594660, 4443983024713710660,
  4443999302145426660, 4444004728353493940, 4697926074230690925, 4888378614051233210, 4951787735545660620, 4951860984882747000,
  5078823014534842040, 5110568269556959755, 5127653938552352760, 5332763351270742660, 5510600805589082112]
private def pivots : Array (Fin 4) := #[1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1,
  2, 1, 0, 1, 0, 0, 0, 0, 1, 3, 1]
private def positions : Array ℕ := #[39, 44, 25, 53, 61, 54, 63, 47, 37, 27, 38, 18,
  17, 24, 55, 36, 52, 60, 45, 26, 62, 16, 46]
private def slots : Array (Fin 23) := #[10, 11, 12, 21, 0, 0, 0, 0,
  9, 19, 2, 13, 0, 0, 0, 0,
  21, 12, 11, 10, 0, 0, 0, 0,
  13, 2, 19, 9, 0, 0, 0, 0,
  0, 0, 0, 0, 15, 8, 10, 0,
  0, 0, 0, 0, 1, 18, 22, 7,
  0, 0, 0, 0, 16, 3, 5, 14,
  0, 0, 0, 0, 17, 4, 20, 6]
private def rep (i : Fin 23) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 38 ^ x.val) % 38]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 27300).toNat) * 54601 ^ x.val
private def label (p : Cell 8) : Fin 23 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 23) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 23 (evenMask 4)) := by
  apply integerModel.partialArray (evenMask 4) rep label (fun i => pivots[i.val]!) 5460 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 4) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B8_23

namespace SmallEven.B8_25
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-48, -36, -24, -12, -8, -6,
  -3, 0, 3, 4, 6, 12,
  18, 24, 36, 48]
private def words : Array ℕ := #[1835, 7607, 8571, 9083, 12983, 22363, 22475, 22711,
  27259, 29355, 30587, 30647, 31051, 31607, 31707, 35451,
  42843, 42955, 43191, 45751, 46967, 53627, 54139, 60855,
  63275]
private def codes : Array ℕ := #[454020, 11635392, 22021776, 22247592, 33087912, 38788032,
  38790360, 38817993, 41583087, 44039418, 44264652, 44265804,
  44301512, 44377548, 44379888, 47059125, 49740108, 49742436,
  49770069, 54992064, 55216716, 65830080, 66055896, 77347848,
  88070628]
private def pivots : Array (Fin 4) := #[0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1,
  0, 2, 0, 0, 0, 0, 1, 1, 3, 0, 0, 1,
  0]
private def positions : Array ℕ := #[18, 44, 45, 25, 60, 62, 10, 16, 53, 55, 36, 37,
  47, 38, 63, 17, 26, 46, 52, 24, 39, 9, 61, 8,
  54]
private def slots : Array (Fin 25) := #[10, 11, 13, 20, 0, 0, 0, 0,
  23, 21, 6, 12, 0, 0, 0, 0,
  7, 15, 0, 9, 0, 0, 0, 0,
  19, 3, 16, 14, 0, 0, 0, 0,
  0, 0, 0, 0, 10, 11, 13, 20,
  0, 0, 0, 0, 1, 2, 17, 12,
  0, 0, 0, 0, 18, 8, 24, 9,
  0, 0, 0, 0, 4, 22, 5, 14]
private def rep (i : Fin 25) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 16 ^ x.val) % 16]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 48).toNat) * 97 ^ x.val
private def label (p : Cell 8) : Fin 25 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 25) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 25 (evenMask 4)) := by
  apply integerModel.partialArray (evenMask 4) rep label (fun i => pivots[i.val]!) 12 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 4) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B8_25

namespace SmallEven.B8_29
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-82764, -60192, -50160, -45144, -37620, -35739,
  -30096, -20064, -18810, -16720, -15048, -12540,
  -10032, -7920, -7524, -6840, -6270, 0,
  2736, 3762, 5016, 6336, 7524, 8360,
  9405, 11286, 12540, 15048, 18810, 22572,
  25080, 30096, 37620, 45144, 50160]
private def words : Array ℕ := #[20992, 63937, 249297, 270122, 303512, 321572, 328642, 338092,
  622117, 624487, 737022, 750322, 750662, 753822, 762562, 763062,
  790747, 842197, 921682, 964592, 1085937, 1093322, 1102422, 1111382,
  1165937, 1179062, 1333422, 1370172, 1453812]
private def codes : Array ℕ := #[2267728644979512, 102376890798927246216, 213283247853207744927, 238875975916351034976, 284374846330026629892, 284376220704418920792,
  284376449764395946672, 284376907900955867712, 341251011302064589440, 341251114379054236038, 375375061030038503148, 375375885654673877688,
  375375885657164743032, 375376023090660093216, 375376297967614270008, 375376297972596045840, 387784743460190277552, 392438528989316885790,
  404112621953443400712, 409500760009774046328, 426562853594037417972, 426563197189192290942, 426563454891007246527, 426564227968429708872,
  443624809743975145968, 443625634367365080312, 511874146141235090928, 511876620018877535136, 580125956421119210784]
private def pivots : Array (Fin 4) := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
  1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 3, 0, 0, 1]
private def positions : Array ℕ := #[62, 18, 53, 25, 55, 36, 47, 63, 46, 16, 19, 0,
  37, 11, 38, 27, 61, 17, 54, 26, 44, 39, 52, 60,
  24, 3, 9, 45, 8]
private def slots : Array (Fin 29) := #[11, 12, 14, 25, 0, 0, 0, 0,
  28, 26, 8, 13, 0, 0, 0, 0,
  9, 17, 1, 10, 0, 0, 0, 0,
  24, 3, 19, 15, 0, 0, 0, 0,
  0, 0, 0, 0, 5, 12, 14, 21,
  0, 0, 0, 0, 20, 27, 8, 6,
  0, 0, 0, 0, 22, 2, 18, 4,
  0, 0, 0, 0, 23, 16, 0, 7]
private def rep (i : Fin 29) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 35 ^ x.val) % 35]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 82764).toNat) * 165529 ^ x.val
private def label (p : Cell 8) : Fin 29 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 29) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 29 (evenMask 4)) := by
  apply integerModel.partialArray (evenMask 4) rep label (fun i => pivots[i.val]!) 15048 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 4) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B8_29

namespace SmallEven.B8_30
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-18480, -12320, -10164, -9240, -7392, -6160,
  -5544, -3696, -3465, -2640, -2464, -1848,
  -1540, -1232, -1155, -924, -264, 0,
  336, 420, 462, 616, 924, 1155,
  1232, 1386, 1540, 1848, 2310, 2772,
  3696, 4620, 5544, 12936]
private def words : Array ℕ := #[51061, 177133, 288449, 343835, 372837, 484289, 610225, 613615,
  675369, 677035, 680333, 688425, 688755, 689649, 692913, 697673,
  699975, 700427, 706343, 812117, 884877, 933701, 968177, 1033899,
  1070235, 1081455, 1103429, 1186661, 1247453, 1293343]
private def codes : Array ℕ := #[311058734115119144, 559891583477678760, 746511171404936784, 758179471403100054, 799833938866817184, 855373228932279904,
  886480280367975216, 886480911479192106, 933128234477496288, 933130759229738916, 933132442249908824, 933135808358552568,
  933135808426854648, 933136267388891244, 933136649840177552, 933137701794664674, 933138332940033528, 933138333076643232,
  933153479745892944, 956464834695810594, 979791336417433848, 991457111953646184, 995344020676424496, 1010891655681377624,
  1026441815449955520, 1026446864544617208, 1049760743392980234, 1119750346986237120, 1166415341918311254, 1213074026148019728]
private def pivots : Array (Fin 4) := #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
  1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
  1, 3, 0, 0, 0, 1]
private def positions : Array ℕ := #[54, 18, 25, 44, 61, 46, 10, 16, 47, 19, 36, 0,
  37, 55, 11, 38, 2, 27, 63, 17, 26, 60, 45, 62,
  24, 39, 53, 9, 52, 8]
private def slots : Array (Fin 30) := #[11, 12, 16, 25, 0, 0, 0, 0,
  29, 27, 6, 14, 0, 0, 0, 0,
  7, 19, 1, 9, 0, 0, 0, 0,
  24, 2, 20, 17, 0, 0, 0, 0,
  0, 0, 0, 0, 10, 12, 15, 25,
  0, 0, 0, 0, 3, 22, 5, 8,
  0, 0, 0, 0, 28, 26, 0, 13,
  0, 0, 0, 0, 21, 4, 23, 18]
private def rep (i : Fin 30) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 34 ^ x.val) % 34]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 18480).toNat) * 36961 ^ x.val
private def label (p : Cell 8) : Fin 30 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 30) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 30 (evenMask 4)) := by
  apply integerModel.partialArray (evenMask 4) rep label (fun i => pivots[i.val]!) 1848 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 4) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B8_30

namespace SmallEven.B8_31
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-23400, -21840, -18720, -16380, -10920, -8580,
  -7800, -7020, -6825, -5460, -3900, -3640,
  -2730, -2100, -1950, -1040, 0, 520,
  546, 1170, 1365, 1560, 1755, 1820,
  1950, 2730, 3120, 3510, 3900, 4200,
  4680, 5460, 6240, 6552, 7800, 8190,
  10920, 16380, 27300]
private def words : Array ℕ := #[83842, 232417, 251620, 385897, 436753, 465262, 503155, 540610,
  638929, 659818, 737560, 743473, 956194, 974095, 974665, 984547,
  996895, 997690, 1225060, 1283092, 1507810, 1519183, 1543573, 1571770,
  1684441, 1741249, 1846198, 1863865, 2016550, 2140702, 2250784]
private def codes : Array ℕ := #[888861716398737900, 1777666460743006470, 2666406092975450280, 3174300331470561540, 3301259647372693110, 3301284064861813680,
  3333009243917752581, 3555170142100766280, 3809153885122500720, 3851430251350600100, 3999592861435200120, 3999596930718593295,
  4443950469104980470, 4443983024415594660, 4443983024713710660, 4443988450126792840, 4443999302145426660, 4443999302741675040,
  4666186244994301755, 4697926074230690925, 4888373187694110660, 4888378614051233210, 4951787735545660620, 4951860984882747000,
  5078823014534842040, 5127653938552352760, 5332730796109189200, 5332763351270742660, 5510600805589082112, 6221494844936389200,
  7110356560738845960]
private def pivots : Array (Fin 4) := #[0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1,
  0, 0, 1, 0, 2, 0, 0, 0, 0, 1, 0, 0,
  0, 1, 1, 3, 1, 0, 1]
private def positions : Array ℕ := #[18, 39, 25, 44, 53, 61, 54, 63, 47, 37, 10, 16,
  19, 38, 1, 11, 2, 27, 17, 55, 26, 36, 52, 60,
  45, 62, 24, 3, 46, 9, 8]
private def slots : Array (Fin 31) := #[13, 14, 16, 27, 0, 0, 0, 0,
  30, 29, 10, 15, 0, 0, 0, 0,
  11, 18, 0, 12, 0, 0, 0, 0,
  26, 2, 20, 17, 0, 0, 0, 0,
  0, 0, 0, 0, 21, 9, 13, 1,
  0, 0, 0, 0, 3, 24, 28, 8,
  0, 0, 0, 0, 22, 4, 6, 19,
  0, 0, 0, 0, 23, 5, 25, 7]
private def rep (i : Fin 31) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 39 ^ x.val) % 39]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 27300).toNat) * 54601 ^ x.val
private def label (p : Cell 8) : Fin 31 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 31) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 31 (evenMask 4)) := by
  apply integerModel.partialArray (evenMask 4) rep label (fun i => pivots[i.val]!) 5460 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 4) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B8_31

