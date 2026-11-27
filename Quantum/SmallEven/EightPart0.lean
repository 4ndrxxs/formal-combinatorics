module
public import Quantum.DiagonalBlocks
public import Quantum.PartialCertificates

@[expose] public section
namespace SmallEven.B8_4
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[0, 1]
private def words : Array ℕ := #[1, 2, 4, 8]
private def codes : Array ℕ := #[41, 43, 49, 67]
private def pivots : Array (Fin 4) := #[0, 1, 2, 3]
private def positions : Array ℕ := #[62, 60, 63, 61]
private def slots : Array (Fin 4) := #[0, 1, 2, 3, 0, 0, 0, 0,
  2, 0, 3, 1, 0, 0, 0, 0,
  3, 2, 1, 0, 0, 0, 0, 0,
  1, 3, 0, 2, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 1, 2, 3,
  0, 0, 0, 0, 2, 0, 3, 1,
  0, 0, 0, 0, 3, 2, 1, 0,
  0, 0, 0, 0, 1, 3, 0, 2]
private def rep (i : Fin 4) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 2 ^ x.val) % 2]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 1).toNat) * 3 ^ x.val
private def label (p : Cell 8) : Fin 4 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 4) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 4 (evenMask 4)) := by
  apply integerModel.partialArray (evenMask 4) rep label (fun i => pivots[i.val]!) 1 (by decide)
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
end SmallEven.B8_4

namespace SmallEven.B8_6
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-16, 0, 9, 12]
private def words : Array ℕ := #[23, 87, 93, 117, 151, 213]
private def codes : Array ℕ := #[17980, 592972, 593356, 606028, 916405, 1024204]
private def pivots : Array (Fin 4) := #[0, 0, 1, 2, 0, 3]
private def positions : Array ℕ := #[62, 26, 60, 63, 61, 25]
private def slots : Array (Fin 6) := #[1, 2, 3, 5, 0, 0, 0, 0,
  3, 1, 5, 2, 0, 0, 0, 0,
  5, 3, 2, 1, 0, 0, 0, 0,
  2, 5, 1, 3, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 2, 3, 4,
  0, 0, 0, 0, 3, 0, 4, 2,
  0, 0, 0, 0, 4, 3, 2, 0,
  0, 0, 0, 0, 2, 4, 0, 3]
private def rep (i : Fin 6) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 4 ^ x.val) % 4]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 16).toNat) * 33 ^ x.val
private def label (p : Cell 8) : Fin 6 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 6) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 6 (evenMask 4)) := by
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
end SmallEven.B8_6

namespace SmallEven.B8_7
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-9, -3, -2, 0, 4, 6,
  12, 18]
private def words : Array ℕ := #[1597, 1677, 1757, 1771, 1883, 1957, 2779]
private def codes : Array ℕ := #[925431, 934237, 937086, 937302, 945294, 953662,
  1240998]
private def pivots : Array (Fin 4) := #[0, 0, 0, 1, 2, 0, 3]
private def positions : Array ℕ := #[62, 60, 26, 24, 27, 61, 63]
private def slots : Array (Fin 7) := #[2, 3, 4, 6, 0, 0, 0, 0,
  4, 2, 6, 3, 0, 0, 0, 0,
  6, 4, 3, 2, 0, 0, 0, 0,
  3, 6, 2, 4, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 1, 6, 5,
  0, 0, 0, 0, 6, 0, 5, 1,
  0, 0, 0, 0, 5, 6, 1, 0,
  0, 0, 0, 0, 1, 5, 0, 6]
private def rep (i : Fin 7) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 8 ^ x.val) % 8]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 18).toNat) * 37 ^ x.val
private def label (p : Cell 8) : Fin 7 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 7) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 7 (evenMask 4)) := by
  apply integerModel.partialArray (evenMask 4) rep label (fun i => pivots[i.val]!) 6 (by decide)
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
end SmallEven.B8_7

namespace SmallEven.B8_9
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-72, -63, -48, -16, 0, 8,
  12, 24, 36, 112]
private def words : Array ℕ := #[187, 487, 987, 3427, 4447, 4474, 4744, 6457,
  7444]
private def codes : Array ℕ := #[458139061, 461328436, 466998436, 1099184536, 1281445336, 1281450712,
  1282660312, 1418134636, 1554820312]
private def pivots : Array (Fin 4) := #[0, 0, 0, 0, 0, 1, 2, 0, 3]
private def positions : Array ℕ := #[61, 52, 62, 63, 26, 24, 55, 60, 25]
private def slots : Array (Fin 9) := #[4, 5, 6, 8, 0, 0, 0, 0,
  6, 4, 8, 5, 0, 0, 0, 0,
  8, 6, 5, 4, 0, 0, 0, 0,
  5, 8, 4, 6, 0, 0, 0, 0,
  0, 0, 0, 0, 6, 7, 3, 1,
  0, 0, 0, 0, 3, 2, 0, 7,
  0, 0, 0, 0, 1, 3, 7, 6,
  0, 0, 0, 0, 7, 0, 2, 3]
private def rep (i : Fin 9) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 10 ^ x.val) % 10]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 112).toNat) * 225 ^ x.val
private def label (p : Cell 8) : Fin 9 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 9) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 9 (evenMask 4)) := by
  apply integerModel.partialArray (evenMask 4) rep label (fun i => pivots[i.val]!) 24 (by decide)
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
end SmallEven.B8_9

namespace SmallEven.B8_13
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-936, -819, -780, -624, -234, -26,
  0, 156, 270, 312, 324, 351,
  468, 702, 1404, 1456]
private def words : Array ℕ := #[9580, 13932, 18284, 26220, 26310, 27750, 35436, 36892,
  36972, 37116, 46700, 50790, 60780]
private def codes : Array ℕ := #[16721819254894, 20578120029220, 30219644151814, 36002440627348, 36002441990164, 36006411873172,
  42679174825894, 43706656048081, 43706658433828, 43706662675156, 44678620963795, 47570681075476,
  70713118842574]
private def pivots : Array (Fin 4) := #[0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 3,
  0]
private def positions : Array ℕ := #[61, 25, 52, 19, 54, 27, 62, 60, 53, 63, 26, 16,
  55]
private def slots : Array (Fin 13) := #[3, 4, 5, 11, 0, 0, 0, 0,
  5, 10, 1, 4, 0, 0, 0, 0,
  11, 5, 4, 3, 0, 0, 0, 0,
  4, 1, 10, 5, 0, 0, 0, 0,
  0, 0, 0, 0, 12, 4, 8, 2,
  0, 0, 0, 0, 9, 6, 0, 7,
  0, 0, 0, 0, 2, 8, 4, 12,
  0, 0, 0, 0, 7, 0, 6, 9]
private def rep (i : Fin 13) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 16 ^ x.val) % 16]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 1456).toNat) * 2913 ^ x.val
private def label (p : Cell 8) : Fin 13 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 13) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 13 (evenMask 4)) := by
  apply integerModel.partialArray (evenMask 4) rep label (fun i => pivots[i.val]!) 468 (by decide)
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
end SmallEven.B8_13

namespace SmallEven.B8_15
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-936, -819, -780, -624, -351, -234,
  -26, 0, 156, 270, 312, 324,
  351, 468, 624, 702, 1404, 1456]
private def words : Array ℕ := #[13747, 19903, 31891, 42361, 43231, 43333, 45169, 45601,
  56191, 58351, 58459, 58639, 72391, 78217, 98311]
private def codes : Array ℕ := #[16721819254894, 20578120029220, 30219644151814, 35999463555445, 36002440627348, 36002441990164,
  36006411873172, 36007736985220, 42679174825894, 43706656048081, 43706658433828, 43706662675156,
  44678620963795, 47570681075476, 70713118842574]
private def pivots : Array (Fin 4) := #[0, 0, 0, 1, 0, 1, 2, 1, 0, 0, 0, 0,
  0, 3, 0]
private def positions : Array ℕ := #[61, 25, 52, 27, 19, 54, 17, 24, 62, 60, 53, 63,
  26, 16, 55]
private def slots : Array (Fin 15) := #[4, 5, 6, 13, 0, 0, 0, 0,
  3, 12, 1, 7, 0, 0, 0, 0,
  13, 6, 5, 4, 0, 0, 0, 0,
  7, 1, 12, 3, 0, 0, 0, 0,
  0, 0, 0, 0, 14, 5, 10, 2,
  0, 0, 0, 0, 11, 8, 0, 9,
  0, 0, 0, 0, 2, 10, 5, 14,
  0, 0, 0, 0, 9, 0, 8, 11]
private def rep (i : Fin 15) (x : Fin 4) : ℤ :=
  alphabet[(words[i.val]! / 18 ^ x.val) % 18]!
private def code (v : Fin 4 → ℤ) : ℕ :=
  ∑ x, ((v x + 1456).toNat) * 2913 ^ x.val
private def label (p : Cell 8) : Fin 15 := slots[p.1.val * 8 + p.2.val]!
private def witness (i : Fin 15) : Cell 8 :=
  (Fin.ofNat 8 (positions[i.val]! / 8), Fin.ofNat 8 (positions[i.val]! % 8))

theorem block : Nonempty (PartialArray 8 4 15 (evenMask 4)) := by
  apply integerModel.partialArray (evenMask 4) rep label (fun i => pivots[i.val]!) 468 (by decide)
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
end SmallEven.B8_15

