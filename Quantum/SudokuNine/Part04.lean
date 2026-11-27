module
public import Quantum.SudokuCertificate
@[expose] public section
namespace SudokuNine
open QuantumSudoku QuantumCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace C16
private def alphabet : Array IQ := #[(-20,0), (-10,0), (0,0), (2,0), (4,0), (5,0), (10,0)]
private def words : Array ℕ := #[5215772, 6509911, 12274712, 13447772, 13451206, 13451230,
  13451398, 13452574, 13459777, 13460806, 13518430, 13921798,
  16392427, 16745374, 21333685, 36510406]
private def codes : Array ℕ := #[52314664157744780246836003550, 52951116815710366327198125940, 53588707124856896870662452350,
  53589465483765732527173094750, 53589465483765892178176634770, 53589465483765892178176651570,
  53589465483765892178204892370, 53589465483765892225677677170, 53589465483765932150303822775,
  53589465483765972027428925970, 53589465483900118771278158770, 53589465709400795181838495570,
  53589655355536769759632506375, 53589844776037841333764656370, 53717135488138880952766569496,
  54227055792912422721640961170]
private def pivots : Array (Fin 9) := #[7, 6, 6, 3, 0, 1, 2, 3, 3, 4, 5, 6,
  6, 7, 6, 8]
private def labels : Array (Fin 16) := #[6, 5, 4, 10, 9, 7, 0, 1, 14,
  10, 9, 7, 15, 2, 12, 6, 5, 4,
  15, 13, 11, 6, 5, 4, 10, 3, 8,
  5, 4, 6, 9, 7, 10, 1, 14, 0,
  9, 7, 10, 2, 12, 15, 5, 4, 6,
  13, 11, 15, 5, 4, 6, 3, 8, 10,
  4, 6, 5, 7, 10, 9, 14, 0, 1,
  7, 10, 9, 12, 15, 2, 4, 6, 5,
  11, 15, 13, 4, 6, 5, 8, 10, 3]
private def locations : Array ℕ := #[6, 7, 13, 25, 2, 1, 0, 5, 26, 4, 3, 20,
  14, 19, 8, 12]
private def rep (i : Fin 16) (x : Fin 9) : IQ :=
  alphabet[(words[i.val]! / 7^x.val) % 7]!
private def lab (r s : Index (Fin 3)) : Fin 16 :=
  labels[(3*r.1.val+r.2.val)*9+3*s.1.val+s.2.val]!
private def pos (k : ℕ) : Index (Fin 3) := (Fin.ofNat 3 (k/3),Fin.ofNat 3 k)
private def code (v : Fin 9 → IQ) : ℕ :=
  ∑ x, (((v x).1+20).toNat + ((v x).2+20).toNat*41)*41^(2*x.val)

theorem realized : Realizes 3 16 := by
  apply of_certificate (imaginaryModel 3 (by decide)) rep lab (fun i => pivots[i.val]!) (10,0) (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have hits : ∀ i : Fin 16, lab (pos (locations[i.val]! / 9)) (pos (locations[i.val]! % 9))=i := by decide +kernel
    exact fun i => ⟨_,_,hits i⟩
  all_goals decide +kernel

end C16


namespace C17
private def alphabet : Array IQ := #[(-4,-4), (-4,4), (-2,0), (0,0), (1,-1), (1,1), (4,0), (8,0)]
private def words : Array ℕ := #[13481691, 80590555, 47036123, 57435867, 57566939, 57501403,
  57521715, 57521886, 57522035, 57523419, 57665243, 57599707,
  57468635, 58308315, 130922203, 97367771, 30258907]
private def codes : Array ℕ := #[3528609922292085568588, 6253636667329430203524, 6934893353588766362258,
  7031542080910204692940, 7031542193805863118084, 7031542222029777724370,
  7031542226033856483148, 7031542226033862495508, 7031542226033864000038,
  7031542226033959045780, 7031542242189716728860, 7031542262349655733350,
  7031542355085375154004, 7031544556522811414548, 7421505272345435047068,
  7908117191102103731878, 10146532017382779682004]
private def pivots : Array (Fin 9) := #[7, 7, 7, 4, 4, 4, 1, 0, 1, 3, 4, 4,
  4, 6, 7, 7, 7]
private def labels : Array (Fin 17) := #[6, 8, 7, 10, 5, 9, 14, 2, 13,
  3, 11, 9, 16, 1, 13, 6, 8, 7,
  0, 15, 13, 6, 8, 7, 12, 4, 9,
  8, 7, 6, 5, 9, 10, 2, 13, 14,
  11, 9, 3, 1, 13, 16, 8, 7, 6,
  15, 13, 0, 8, 7, 6, 4, 9, 12,
  7, 6, 8, 9, 10, 5, 13, 14, 2,
  9, 3, 11, 13, 16, 1, 7, 6, 8,
  13, 0, 15, 7, 6, 8, 9, 12, 4]
private def locations : Array ℕ := #[18, 13, 7, 9, 25, 4, 0, 2, 1, 5, 3, 10,
  24, 8, 6, 19, 12]
private def rep (i : Fin 17) (x : Fin 9) : IQ :=
  alphabet[(words[i.val]! / 8^x.val) % 8]!
private def lab (r s : Index (Fin 3)) : Fin 17 :=
  labels[(3*r.1.val+r.2.val)*9+3*s.1.val+s.2.val]!
private def pos (k : ℕ) : Index (Fin 3) := (Fin.ofNat 3 (k/3),Fin.ofNat 3 k)
private def code (v : Fin 9 → IQ) : ℕ :=
  ∑ x, (((v x).1+8).toNat + ((v x).2+8).toNat*17)*17^(2*x.val)

theorem realized : Realizes 3 17 := by
  apply of_certificate (imaginaryModel 3 (by decide)) rep lab (fun i => pivots[i.val]!) (4,0) (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have hits : ∀ i : Fin 17, lab (pos (locations[i.val]! / 9)) (pos (locations[i.val]! % 9))=i := by decide +kernel
    exact fun i => ⟨_,_,hits i⟩
  all_goals decide +kernel

end C17


namespace C18
private def alphabet : Array IQ := #[(-1,-1), (-1,1), (0,0), (2,0)]
private def words : Array ℕ := #[42682, 141742, 166507, 174763, 174766, 174778,
  174826, 175018, 175786, 178858, 178923, 170539,
  191146, 191406, 157870, 240298, 241338, 107194]
private def codes : Array ℕ := #[991860352812, 1870729101612, 1905883851564,
  1907348632814, 1907348632862, 1907348634062,
  1907348664062, 1907349414062, 1907368164062,
  1907836914062, 1907836945314, 1908325101564,
  1919555664062, 1919556445362, 1931760351612,
  2212524414062, 2212543946562, 2517641602812]
private def pivots : Array (Fin 9) := #[2, 1, 0, 0, 1, 2, 3, 4, 5, 6, 0, 0,
  7, 1, 1, 8, 2, 2]
private def labels : Array (Fin 18) := #[5, 4, 3, 8, 7, 6, 15, 12, 9,
  8, 7, 6, 15, 12, 9, 5, 4, 3,
  15, 12, 9, 5, 4, 3, 8, 7, 6,
  13, 10, 16, 1, 2, 17, 14, 11, 0,
  1, 2, 0, 14, 11, 16, 13, 10, 17,
  14, 11, 17, 13, 10, 0, 1, 2, 16,
  3, 5, 4, 6, 8, 7, 9, 15, 12,
  6, 8, 7, 9, 15, 12, 3, 5, 4,
  9, 15, 12, 3, 5, 4, 6, 8, 7]
private def locations : Array ℕ := #[35, 30, 31, 2, 1, 0, 5, 4, 3, 8, 28, 34,
  7, 27, 33, 6, 29, 32]
private def rep (i : Fin 18) (x : Fin 9) : IQ :=
  alphabet[(words[i.val]! / 4^x.val) % 4]!
private def lab (r s : Index (Fin 3)) : Fin 18 :=
  labels[(3*r.1.val+r.2.val)*9+3*s.1.val+s.2.val]!
private def pos (k : ℕ) : Index (Fin 3) := (Fin.ofNat 3 (k/3),Fin.ofNat 3 k)
private def code (v : Fin 9 → IQ) : ℕ :=
  ∑ x, (((v x).1+2).toNat + ((v x).2+2).toNat*5)*5^(2*x.val)

theorem realized : Realizes 3 18 := by
  apply of_certificate (imaginaryModel 3 (by decide)) rep lab (fun i => pivots[i.val]!) (2,0) (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have hits : ∀ i : Fin 18, lab (pos (locations[i.val]! / 9)) (pos (locations[i.val]! % 9))=i := by decide +kernel
    exact fun i => ⟨_,_,hits i⟩
  all_goals decide +kernel

end C18


namespace C19
private def alphabet : Array IQ := #[(-4,-4), (-4,4), (-2,0), (0,0), (1,-1), (1,1), (4,0), (8,0)]
private def words : Array ℕ := #[80590555, 47036123, 57566939, 57501403, 57521715, 57521886,
  57521907, 57522075, 57522035, 57523419, 57534171, 57620187,
  57665243, 57468635, 58308315, 63813339, 107853531, 130922203,
  30258907]
private def codes : Array ℕ := #[6253636667329430203524, 6934893353588766362258, 7031542193805863118084,
  7031542222029777724370, 7031542226033856483148, 7031542226033862495508,
  7031542226033862496660, 7031542226033862829588, 7031542226033864000038,
  7031542226033959045780, 7031542226061765525268, 7031542234097838097300,
  7031542242189716728860, 7031542355085375154004, 7031544556522811414548,
  7032215737340100099220, 7226186993536529969428, 7421505272345435047068,
  10146532017382779682004]
private def pivots : Array (Fin 9) := #[7, 7, 4, 4, 1, 0, 1, 2, 1, 3, 4, 5,
  4, 4, 6, 7, 8, 7, 7]
private def labels : Array (Fin 19) := #[7, 6, 5, 12, 3, 9, 17, 1, 14,
  11, 10, 9, 18, 0, 14, 4, 8, 5,
  16, 15, 14, 4, 8, 5, 13, 2, 9,
  6, 5, 7, 3, 9, 12, 1, 14, 17,
  10, 9, 11, 0, 14, 18, 8, 5, 4,
  15, 14, 16, 8, 5, 4, 2, 9, 13,
  5, 7, 6, 9, 12, 3, 14, 17, 1,
  9, 11, 10, 14, 18, 0, 5, 4, 8,
  14, 16, 15, 5, 4, 8, 9, 13, 2]
private def locations : Array ℕ := #[13, 7, 25, 4, 15, 2, 1, 0, 16, 5, 10, 9,
  3, 24, 8, 19, 18, 6, 12]
private def rep (i : Fin 19) (x : Fin 9) : IQ :=
  alphabet[(words[i.val]! / 8^x.val) % 8]!
private def lab (r s : Index (Fin 3)) : Fin 19 :=
  labels[(3*r.1.val+r.2.val)*9+3*s.1.val+s.2.val]!
private def pos (k : ℕ) : Index (Fin 3) := (Fin.ofNat 3 (k/3),Fin.ofNat 3 k)
private def code (v : Fin 9 → IQ) : ℕ :=
  ∑ x, (((v x).1+8).toNat + ((v x).2+8).toNat*17)*17^(2*x.val)

theorem realized : Realizes 3 19 := by
  apply of_certificate (imaginaryModel 3 (by decide)) rep lab (fun i => pivots[i.val]!) (4,0) (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have hits : ∀ i : Fin 19, lab (pos (locations[i.val]! / 9)) (pos (locations[i.val]! % 9))=i := by decide +kernel
    exact fun i => ⟨_,_,hits i⟩
  all_goals decide +kernel

end C19

end SudokuNine
