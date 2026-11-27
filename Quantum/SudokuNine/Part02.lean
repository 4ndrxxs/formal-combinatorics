module
public import Quantum.SudokuCertificate
@[expose] public section
namespace SudokuNine
open QuantumSudoku QuantumCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace C9
private def alphabet : Array IQ := #[(0,0), (1,0)]
private def words : Array ℕ := #[1, 2, 4, 8, 16, 32,
  64, 128, 256]
private def codes : Array ℕ := #[193710245, 193710253, 193710325,
  193710973, 193716805, 193769293,
  194241685, 198493213, 236756965]
private def pivots : Array (Fin 9) := #[0, 1, 2, 3, 4, 5, 6, 7, 8]
private def labels : Array (Fin 9) := #[2, 1, 0, 5, 4, 3, 8, 7, 6,
  5, 4, 3, 8, 7, 6, 2, 1, 0,
  8, 7, 6, 2, 1, 0, 5, 4, 3,
  1, 0, 2, 4, 3, 5, 7, 6, 8,
  4, 3, 5, 7, 6, 8, 1, 0, 2,
  7, 6, 8, 1, 0, 2, 4, 3, 5,
  0, 2, 1, 3, 5, 4, 6, 8, 7,
  3, 5, 4, 6, 8, 7, 0, 2, 1,
  6, 8, 7, 0, 2, 1, 3, 5, 4]
private def locations : Array ℕ := #[2, 1, 0, 5, 4, 3, 8, 7, 6]
private def rep (i : Fin 9) (x : Fin 9) : IQ :=
  alphabet[(words[i.val]! / 2^x.val) % 2]!
private def lab (r s : Index (Fin 3)) : Fin 9 :=
  labels[(3*r.1.val+r.2.val)*9+3*s.1.val+s.2.val]!
private def pos (k : ℕ) : Index (Fin 3) := (Fin.ofNat 3 (k/3),Fin.ofNat 3 k)
private def code (v : Fin 9 → IQ) : ℕ :=
  ∑ x, (((v x).1+1).toNat + ((v x).2+1).toNat*3)*3^(2*x.val)

theorem realized : Realizes 3 9 := by
  apply of_certificate (imaginaryModel 3 (by decide)) rep lab (fun i => pivots[i.val]!) (1,0) (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have hits : ∀ i : Fin 9, lab (pos (locations[i.val]! / 9)) (pos (locations[i.val]! % 9))=i := by decide +kernel
    exact fun i => ⟨_,_,hits i⟩
  all_goals decide +kernel

end C9


namespace C11
private def alphabet : Array IQ := #[(-4,0), (0,0), (1,0), (2,0)]
private def words : Array ℕ := #[79189, 87383, 87389, 87413, 87509, 87893,
  89429, 95573, 111957, 120149, 218453]
private def codes : Array ℕ := #[74956375337752678, 75047317648499562, 75047317648499722,
  75047317648512682, 75047317649562442, 75047317734593002,
  75047324622068362, 75047882507572522, 75070759300027483,
  75093071233409482, 78753358026203242]
private def pivots : Array (Fin 9) := #[6, 0, 1, 2, 3, 4, 5, 6, 6, 7, 8]
private def labels : Array (Fin 11) := #[3, 2, 1, 6, 5, 4, 10, 0, 8,
  6, 5, 4, 10, 9, 7, 3, 2, 1,
  10, 9, 7, 3, 2, 1, 6, 5, 4,
  2, 1, 3, 5, 4, 6, 0, 8, 10,
  5, 4, 6, 9, 7, 10, 2, 1, 3,
  9, 7, 10, 2, 1, 3, 5, 4, 6,
  1, 3, 2, 4, 6, 5, 8, 10, 0,
  4, 6, 5, 7, 10, 9, 1, 3, 2,
  7, 10, 9, 1, 3, 2, 4, 6, 5]
private def locations : Array ℕ := #[7, 2, 1, 0, 5, 4, 3, 14, 8, 13, 6]
private def rep (i : Fin 11) (x : Fin 9) : IQ :=
  alphabet[(words[i.val]! / 4^x.val) % 4]!
private def lab (r s : Index (Fin 3)) : Fin 11 :=
  labels[(3*r.1.val+r.2.val)*9+3*s.1.val+s.2.val]!
private def pos (k : ℕ) : Index (Fin 3) := (Fin.ofNat 3 (k/3),Fin.ofNat 3 k)
private def code (v : Fin 9 → IQ) : ℕ :=
  ∑ x, (((v x).1+4).toNat + ((v x).2+4).toNat*9)*9^(2*x.val)

theorem realized : Realizes 3 11 := by
  apply of_certificate (imaginaryModel 3 (by decide)) rep lab (fun i => pivots[i.val]!) (2,0) (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have hits : ∀ i : Fin 11, lab (pos (locations[i.val]! / 9)) (pos (locations[i.val]! % 9))=i := by decide +kernel
    exact fun i => ⟨_,_,hits i⟩
  all_goals decide +kernel

end C11

end SudokuNine
