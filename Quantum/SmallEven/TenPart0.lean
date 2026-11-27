module
public import Quantum.DiagonalBlocks
public import Quantum.PartialCertificates

@[expose] public section
namespace SmallEven.B10_5
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[0, 1]
private def words : Array ℕ := #[1, 2, 4, 8, 16]
private def codes : Array ℕ := #[122, 124, 130, 148, 202]
private def pivots : Array (Fin 5) := #[0, 1, 2, 3, 4]
private def positions : Array ℕ := #[99, 98, 96, 97, 95]
private def slots : Array (Fin 5) := #[0, 1, 2, 3, 4, 0, 0, 0, 0, 0,
  1, 0, 4, 2, 3, 0, 0, 0, 0, 0,
  3, 4, 1, 0, 2, 0, 0, 0, 0, 0,
  2, 3, 0, 4, 1, 0, 0, 0, 0, 0,
  4, 2, 3, 1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1, 2, 3, 4,
  0, 0, 0, 0, 0, 1, 0, 4, 2, 3,
  0, 0, 0, 0, 0, 3, 4, 1, 0, 2,
  0, 0, 0, 0, 0, 2, 3, 0, 4, 1,
  0, 0, 0, 0, 0, 4, 2, 3, 1, 0]
private def rep (i : Fin 5) (x : Fin 5) : ℤ :=
  alphabet[(words[i.val]! / 2 ^ x.val) % 2]!
private def code (v : Fin 5 → ℤ) : ℕ :=
  ∑ x, ((v x + 1).toNat) * 3 ^ x.val
private def label (p : Cell 10) : Fin 5 := slots[p.1.val * 10 + p.2.val]!
private def witness (i : Fin 5) : Cell 10 :=
  (Fin.ofNat 10 (positions[i.val]! / 10), Fin.ofNat 10 (positions[i.val]! % 10))

theorem block : Nonempty (PartialArray 10 5 5 (evenMask 5)) := by
  apply integerModel.partialArray (evenMask 5) rep label (fun i => pivots[i.val]!) 1 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 5) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B10_5

namespace SmallEven.B10_7
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-9, 0, 12, 16]
private def words : Array ℕ := #[326, 342, 345, 357, 374, 405, 597]
private def codes : Array ℕ := #[19557907, 19567708, 19568092, 19580764, 19585132, 19998940,
  33798748]
private def pivots : Array (Fin 5) := #[0, 0, 1, 2, 0, 3, 4]
private def positions : Array ℕ := #[96, 44, 98, 41, 99, 97, 95]
private def slots : Array (Fin 7) := #[1, 2, 3, 5, 6, 0, 0, 0, 0, 0,
  2, 1, 6, 3, 5, 0, 0, 0, 0, 0,
  5, 6, 2, 1, 3, 0, 0, 0, 0, 0,
  3, 5, 1, 6, 2, 0, 0, 0, 0, 0,
  6, 3, 5, 2, 1, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 4, 2, 0, 5, 6,
  0, 0, 0, 0, 0, 2, 4, 6, 0, 5,
  0, 0, 0, 0, 0, 5, 6, 2, 4, 0,
  0, 0, 0, 0, 0, 0, 5, 4, 6, 2,
  0, 0, 0, 0, 0, 6, 0, 5, 2, 4]
private def rep (i : Fin 7) (x : Fin 5) : ℤ :=
  alphabet[(words[i.val]! / 4 ^ x.val) % 4]!
private def code (v : Fin 5 → ℤ) : ℕ :=
  ∑ x, ((v x + 16).toNat) * 33 ^ x.val
private def label (p : Cell 10) : Fin 7 := slots[p.1.val * 10 + p.2.val]!
private def witness (i : Fin 7) : Cell 10 :=
  (Fin.ofNat 10 (positions[i.val]! / 10), Fin.ofNat 10 (positions[i.val]! % 10))

theorem block : Nonempty (PartialArray 10 5 7 (evenMask 5)) := by
  apply integerModel.partialArray (evenMask 5) rep label (fun i => pivots[i.val]!) 12 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 5) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B10_7

namespace SmallEven.B10_8
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-18, -12, -4, 0, 2, 3,
  6, 9]
private def words : Array ℕ := #[2035, 9843, 14046, 14067, 14235, 15579, 22323, 26331]
private def codes : Array ℕ := #[949623, 27159128, 34671984, 34672200, 34680192, 34975896,
  40297421, 45916944]
private def pivots : Array (Fin 5) := #[1, 1, 0, 1, 2, 3, 1, 4]
private def positions : Array ℕ := #[95, 98, 99, 43, 41, 97, 96, 40]
private def slots : Array (Fin 8) := #[2, 3, 4, 5, 7, 0, 0, 0, 0, 0,
  3, 2, 7, 4, 5, 0, 0, 0, 0, 0,
  5, 7, 3, 2, 4, 0, 0, 0, 0, 0,
  4, 5, 2, 7, 3, 0, 0, 0, 0, 0,
  7, 4, 5, 3, 2, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 2, 1, 6, 5, 0,
  0, 0, 0, 0, 0, 1, 2, 0, 6, 5,
  0, 0, 0, 0, 0, 5, 0, 1, 2, 6,
  0, 0, 0, 0, 0, 6, 5, 2, 0, 1,
  0, 0, 0, 0, 0, 0, 6, 5, 1, 2]
private def rep (i : Fin 8) (x : Fin 5) : ℤ :=
  alphabet[(words[i.val]! / 8 ^ x.val) % 8]!
private def code (v : Fin 5 → ℤ) : ℕ :=
  ∑ x, ((v x + 18).toNat) * 37 ^ x.val
private def label (p : Cell 10) : Fin 8 := slots[p.1.val * 10 + p.2.val]!
private def witness (i : Fin 8) : Cell 10 :=
  (Fin.ofNat 10 (positions[i.val]! / 10), Fin.ofNat 10 (positions[i.val]! % 10))

theorem block : Nonempty (PartialArray 10 5 8 (evenMask 5)) := by
  apply integerModel.partialArray (evenMask 5) rep label (fun i => pivots[i.val]!) 6 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 5) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B10_8

namespace SmallEven.B10_9
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-56, -24, -22, -12, -6, 0,
  1, 4, 8, 12, 16]
private def words : Array ℕ := #[39323, 49872, 80529, 80569, 81009, 85849, 117852, 127125,
  139089]
private def codes : Array ℕ := #[5630907362, 7246947482, 9212175908, 9212177252, 9212329124, 9229490660,
  10435754372, 10522326497, 11168744228]
private def pivots : Array (Fin 5) := #[0, 0, 0, 1, 2, 3, 0, 0, 4]
private def positions : Array ℕ := #[98, 97, 44, 43, 96, 42, 99, 95, 40]
private def slots : Array (Fin 9) := #[2, 3, 4, 5, 8, 0, 0, 0, 0, 0,
  3, 2, 8, 4, 5, 0, 0, 0, 0, 0,
  5, 8, 3, 2, 4, 0, 0, 0, 0, 0,
  4, 5, 2, 8, 3, 0, 0, 0, 0, 0,
  8, 4, 5, 3, 2, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 6, 0, 4, 1, 7,
  0, 0, 0, 0, 0, 0, 6, 7, 4, 1,
  0, 0, 0, 0, 0, 1, 7, 0, 6, 4,
  0, 0, 0, 0, 0, 4, 1, 6, 7, 0,
  0, 0, 0, 0, 0, 7, 4, 1, 0, 6]
private def rep (i : Fin 9) (x : Fin 5) : ℤ :=
  alphabet[(words[i.val]! / 11 ^ x.val) % 11]!
private def code (v : Fin 5 → ℤ) : ℕ :=
  ∑ x, ((v x + 56).toNat) * 113 ^ x.val
private def label (p : Cell 10) : Fin 9 := slots[p.1.val * 10 + p.2.val]!
private def witness (i : Fin 9) : Cell 10 :=
  (Fin.ofNat 10 (positions[i.val]! / 10), Fin.ofNat 10 (positions[i.val]! % 10))

theorem block : Nonempty (PartialArray 10 5 9 (evenMask 5)) := by
  apply integerModel.partialArray (evenMask 5) rep label (fun i => pivots[i.val]!) 12 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 5) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B10_9

namespace SmallEven.B10_11
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-13468, -5291, -4588, -2964, -1924, -74,
  0, 962, 1924, 2886, 3848, 4082,
  15392, 30784, 46176]
private def words : Array ℕ := #[82465, 325450, 325506, 326346, 338946, 416650, 419965, 423265,
  436735, 527946, 706915]
private def codes : Array ℕ := #[2974224013727731357306181, 3359116317487869889242344, 3359116317487870244612840, 3359116317520689776029928, 3359119348502874738357992, 3499075647158538654258506,
  3499076466351782919933226, 3499077923570534738681526, 3499080255120537648678806, 3639039646230700622052584, 5598539319610575362686376]
private def pivots : Array (Fin 5) := #[0, 0, 1, 2, 3, 0, 0, 0, 0, 4, 0]
private def positions : Array ℕ := #[95, 44, 43, 97, 42, 96, 87, 99, 85, 40, 98]
private def slots : Array (Fin 11) := #[1, 2, 3, 4, 9, 0, 0, 0, 0, 0,
  2, 1, 9, 3, 4, 0, 0, 0, 0, 0,
  4, 9, 2, 1, 3, 0, 0, 0, 0, 0,
  3, 4, 1, 9, 2, 0, 0, 0, 0, 0,
  9, 3, 4, 2, 1, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 6, 10, 8, 3, 0,
  0, 0, 0, 0, 0, 10, 7, 0, 5, 3,
  0, 0, 0, 0, 0, 3, 0, 10, 7, 5,
  0, 0, 0, 0, 0, 8, 3, 6, 0, 10,
  0, 0, 0, 0, 0, 0, 5, 3, 10, 7]
private def rep (i : Fin 11) (x : Fin 5) : ℤ :=
  alphabet[(words[i.val]! / 15 ^ x.val) % 15]!
private def code (v : Fin 5 → ℤ) : ℕ :=
  ∑ x, ((v x + 46176).toNat) * 92353 ^ x.val
private def label (p : Cell 10) : Fin 11 := slots[p.1.val * 10 + p.2.val]!
private def witness (i : Fin 11) : Cell 10 :=
  (Fin.ofNat 10 (positions[i.val]! / 10), Fin.ofNat 10 (positions[i.val]! % 10))

theorem block : Nonempty (PartialArray 10 5 11 (evenMask 5)) := by
  apply integerModel.partialArray (evenMask 5) rep label (fun i => pivots[i.val]!) 3848 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 5) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B10_11

namespace SmallEven.B10_13
open QuantumCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def alphabet : Array ℤ := #[-202020, -79365, -68820, -44460, -30784, -28860,
  -1110, 0, 14430, 28860, 43290, 57720,
  61230, 108225, 230880, 461760, 692640]
private def words : Array ℕ := #[134821, 620324, 621191, 621255, 622343, 622925, 640839, 768666,
  778424, 783235, 802853, 955271, 1333695]
private def codes : Array ℕ := #[2258432671639832329708788638475, 2550700060888774609766788657496, 2550700060888833684368961472920, 2550700060888833684448919834520, 2550700060888944449248035444120, 2550700060889041368517225277145,
  2550700214329316132918817741720, 2656979035181596595169551601750, 2656979076651997256874951890550, 2656979150421459972408596635050, 2656979268452600317262428226250, 2763258245855643277890819367320,
  4251167381909099815461934685400]
private def pivots : Array (Fin 5) := #[0, 0, 0, 1, 2, 0, 3, 0, 0, 0, 0, 4,
  0]
private def positions : Array ℕ := #[95, 41, 32, 43, 97, 44, 42, 96, 87, 99, 85, 40,
  98]
private def slots : Array (Fin 13) := #[2, 3, 4, 6, 11, 0, 0, 0, 0, 0,
  3, 5, 11, 1, 6, 0, 0, 0, 0, 0,
  6, 11, 3, 5, 1, 0, 0, 0, 0, 0,
  4, 6, 2, 11, 3, 0, 0, 0, 0, 0,
  11, 1, 6, 3, 5, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 8, 12, 10, 4, 0,
  0, 0, 0, 0, 0, 12, 9, 0, 7, 4,
  0, 0, 0, 0, 0, 4, 0, 12, 9, 7,
  0, 0, 0, 0, 0, 10, 4, 8, 0, 12,
  0, 0, 0, 0, 0, 0, 7, 4, 12, 9]
private def rep (i : Fin 13) (x : Fin 5) : ℤ :=
  alphabet[(words[i.val]! / 17 ^ x.val) % 17]!
private def code (v : Fin 5 → ℤ) : ℕ :=
  ∑ x, ((v x + 692640).toNat) * 1385281 ^ x.val
private def label (p : Cell 10) : Fin 13 := slots[p.1.val * 10 + p.2.val]!
private def witness (i : Fin 13) : Cell 10 :=
  (Fin.ofNat 10 (positions[i.val]! / 10), Fin.ofNat 10 (positions[i.val]! % 10))

theorem block : Nonempty (PartialArray 10 5 13 (evenMask 5)) := by
  apply integerModel.partialArray (evenMask 5) rep label (fun i => pivots[i.val]!) 57720 (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have h : ∀ i, (evenMask 5) (witness i) = true ∧ label (witness i) = i := by decide +kernel
    exact fun i => ⟨witness i,h i⟩
  all_goals decide +kernel

#print axioms block
end SmallEven.B10_13

