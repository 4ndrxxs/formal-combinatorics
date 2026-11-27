module
public import Quantum.SudokuCertificate
@[expose] public section
namespace SudokuNine
open QuantumSudoku QuantumCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace C12
private def alphabet : Array IQ := #[(-10,0), (-5,0), (0,0), (1,0), (2,0), (5,0)]
private def words : Array ℕ := #[1511654, 1931558, 4031081, 4031096, 4031186, 4031726,
  4034966, 4054406, 4171046, 4870886, 6410534, 9069926]
private def codes : Array ℕ := #[301150928895600519154975, 308255150326960180099570, 315440396198357764894785,
  315440396198357764896985, 315440396198357765867185, 315440396198358193725385,
  315440396198546879191585, 315440396281757169785785, 315440432977495321827985,
  315456615798020372438185, 316877489507602350173668, 322593239649567691536385]
private def pivots : Array (Fin 9) := #[7, 6, 0, 1, 2, 3, 4, 5, 6, 7, 6, 8]
private def labels : Array (Fin 12) := #[4, 3, 2, 7, 6, 5, 0, 1, 10,
  7, 6, 5, 11, 9, 8, 4, 3, 2,
  11, 9, 8, 4, 3, 2, 7, 6, 5,
  3, 2, 4, 6, 5, 7, 1, 10, 0,
  6, 5, 7, 9, 8, 11, 3, 2, 4,
  9, 8, 11, 3, 2, 4, 6, 5, 7,
  2, 4, 3, 5, 7, 6, 10, 0, 1,
  5, 7, 6, 8, 11, 9, 2, 4, 3,
  8, 11, 9, 2, 4, 3, 5, 7, 6]
private def locations : Array ℕ := #[6, 7, 2, 1, 0, 5, 4, 3, 14, 13, 8, 12]
private def rep (i : Fin 12) (x : Fin 9) : IQ :=
  alphabet[(words[i.val]! / 6^x.val) % 6]!
private def lab (r s : Index (Fin 3)) : Fin 12 :=
  labels[(3*r.1.val+r.2.val)*9+3*s.1.val+s.2.val]!
private def pos (k : ℕ) : Index (Fin 3) := (Fin.ofNat 3 (k/3),Fin.ofNat 3 k)
private def code (v : Fin 9 → IQ) : ℕ :=
  ∑ x, (((v x).1+10).toNat + ((v x).2+10).toNat*21)*21^(2*x.val)

theorem realized : Realizes 3 12 := by
  apply of_certificate (imaginaryModel 3 (by decide)) rep lab (fun i => pivots[i.val]!) (5,0) (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have hits : ∀ i : Fin 12, lab (pos (locations[i.val]! / 9)) (pos (locations[i.val]! % 9))=i := by decide +kernel
    exact fun i => ⟨_,_,hits i⟩
  all_goals decide +kernel

end C12


namespace C13
private def alphabet : Array IQ := #[(-4,0), (-2,0), (0,0), (1,0), (2,0)]
private def words : Array ℕ := #[851562, 929687, 976564, 976572, 976612, 976812,
  977812, 982812, 1007812, 1085937, 1132812, 1164062,
  1757812]
private def codes : Array ℕ := #[74956375337752678, 75002128922662600, 75047317648499562,
  75047317648499722, 75047317648512682, 75047317649562442,
  75047317734593002, 75047324622068362, 75047882507572522,
  75070759300027483, 75093071233409482, 75093636092482444,
  78753358026203242]
private def pivots : Array (Fin 9) := #[6, 6, 0, 1, 2, 3, 4, 5, 6, 6, 7, 6,
  8]
private def labels : Array (Fin 13) := #[4, 3, 2, 7, 6, 5, 12, 1, 11,
  7, 6, 5, 12, 0, 9, 4, 3, 2,
  12, 10, 8, 4, 3, 2, 7, 6, 5,
  3, 2, 4, 6, 5, 7, 1, 11, 12,
  6, 5, 7, 0, 9, 12, 3, 2, 4,
  10, 8, 12, 3, 2, 4, 6, 5, 7,
  2, 4, 3, 5, 7, 6, 11, 12, 1,
  5, 7, 6, 9, 12, 0, 2, 4, 3,
  8, 12, 10, 2, 4, 3, 5, 7, 6]
private def locations : Array ℕ := #[13, 7, 2, 1, 0, 5, 4, 3, 20, 14, 19, 8,
  6]
private def rep (i : Fin 13) (x : Fin 9) : IQ :=
  alphabet[(words[i.val]! / 5^x.val) % 5]!
private def lab (r s : Index (Fin 3)) : Fin 13 :=
  labels[(3*r.1.val+r.2.val)*9+3*s.1.val+s.2.val]!
private def pos (k : ℕ) : Index (Fin 3) := (Fin.ofNat 3 (k/3),Fin.ofNat 3 k)
private def code (v : Fin 9 → IQ) : ℕ :=
  ∑ x, (((v x).1+4).toNat + ((v x).2+4).toNat*9)*9^(2*x.val)

theorem realized : Realizes 3 13 := by
  apply of_certificate (imaginaryModel 3 (by decide)) rep lab (fun i => pivots[i.val]!) (2,0) (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have hits : ∀ i : Fin 13, lab (pos (locations[i.val]! / 9)) (pos (locations[i.val]! % 9))=i := by decide +kernel
    exact fun i => ⟨_,_,hits i⟩
  all_goals decide +kernel

end C13


namespace C14
private def alphabet : Array IQ := #[(-20,0), (-10,0), (0,0), (2,0), (4,0), (5,0), (10,0)]
private def words : Array ℕ := #[5215772, 6509911, 12274712, 13451206, 13451230, 13451398,
  13452574, 13460806, 13518430, 13921798, 16392427, 16745374,
  21333685, 36510406]
private def codes : Array ℕ := #[52314664157744780246836003550, 52951116815710366327198125940, 53588707124856896870662452350,
  53589465483765892178176634770, 53589465483765892178176651570, 53589465483765892178204892370,
  53589465483765892225677677170, 53589465483765972027428925970, 53589465483900118771278158770,
  53589465709400795181838495570, 53589655355536769759632506375, 53589844776037841333764656370,
  53717135488138880952766569496, 54227055792912422721640961170]
private def pivots : Array (Fin 9) := #[7, 6, 6, 0, 1, 2, 3, 4, 5, 6, 6, 7,
  6, 8]
private def labels : Array (Fin 14) := #[5, 4, 3, 8, 7, 6, 0, 1, 12,
  8, 7, 6, 13, 2, 10, 5, 4, 3,
  13, 11, 9, 5, 4, 3, 8, 7, 6,
  4, 3, 5, 7, 6, 8, 1, 12, 0,
  7, 6, 8, 2, 10, 13, 4, 3, 5,
  11, 9, 13, 4, 3, 5, 7, 6, 8,
  3, 5, 4, 6, 8, 7, 12, 0, 1,
  6, 8, 7, 10, 13, 2, 3, 5, 4,
  9, 13, 11, 3, 5, 4, 6, 8, 7]
private def locations : Array ℕ := #[6, 7, 13, 2, 1, 0, 5, 4, 3, 20, 14, 19,
  8, 12]
private def rep (i : Fin 14) (x : Fin 9) : IQ :=
  alphabet[(words[i.val]! / 7^x.val) % 7]!
private def lab (r s : Index (Fin 3)) : Fin 14 :=
  labels[(3*r.1.val+r.2.val)*9+3*s.1.val+s.2.val]!
private def pos (k : ℕ) : Index (Fin 3) := (Fin.ofNat 3 (k/3),Fin.ofNat 3 k)
private def code (v : Fin 9 → IQ) : ℕ :=
  ∑ x, (((v x).1+20).toNat + ((v x).2+20).toNat*41)*41^(2*x.val)

theorem realized : Realizes 3 14 := by
  apply of_certificate (imaginaryModel 3 (by decide)) rep lab (fun i => pivots[i.val]!) (10,0) (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have hits : ∀ i : Fin 14, lab (pos (locations[i.val]! / 9)) (pos (locations[i.val]! % 9))=i := by decide +kernel
    exact fun i => ⟨_,_,hits i⟩
  all_goals decide +kernel

end C14


namespace C15
private def alphabet : Array IQ := #[(-4,0), (0,0), (1,0), (2,0)]
private def words : Array ℕ := #[79189, 87253, 87379, 87383, 87387, 87389,
  87413, 87509, 87765, 87893, 89429, 95573,
  111957, 120149, 218453]
private def codes : Array ℕ := #[74956375337752678, 75047317477375558, 75047317648499238,
  75047317648499562, 75047317648499643, 75047317648499722,
  75047317648512682, 75047317649562442, 75047317692609163,
  75047317734593002, 75047324622068362, 75047882507572522,
  75070759300027483, 75093071233409482, 78753358026203242]
private def pivots : Array (Fin 9) := #[6, 3, 0, 0, 0, 1, 2, 3, 3, 4, 5, 6,
  6, 7, 8]
private def labels : Array (Fin 15) := #[6, 5, 3, 10, 9, 7, 14, 0, 12,
  10, 9, 7, 14, 13, 11, 6, 2, 4,
  14, 13, 11, 6, 5, 3, 10, 1, 8,
  5, 3, 6, 9, 7, 10, 0, 12, 14,
  9, 7, 10, 13, 11, 14, 2, 4, 6,
  13, 11, 14, 5, 3, 6, 1, 8, 10,
  3, 6, 5, 7, 10, 9, 12, 14, 0,
  7, 10, 9, 11, 14, 13, 4, 6, 2,
  11, 14, 13, 3, 6, 5, 8, 10, 1]
private def locations : Array ℕ := #[7, 25, 16, 2, 17, 1, 0, 5, 26, 4, 3, 14,
  8, 13, 6]
private def rep (i : Fin 15) (x : Fin 9) : IQ :=
  alphabet[(words[i.val]! / 4^x.val) % 4]!
private def lab (r s : Index (Fin 3)) : Fin 15 :=
  labels[(3*r.1.val+r.2.val)*9+3*s.1.val+s.2.val]!
private def pos (k : ℕ) : Index (Fin 3) := (Fin.ofNat 3 (k/3),Fin.ofNat 3 k)
private def code (v : Fin 9 → IQ) : ℕ :=
  ∑ x, (((v x).1+4).toNat + ((v x).2+4).toNat*9)*9^(2*x.val)

theorem realized : Realizes 3 15 := by
  apply of_certificate (imaginaryModel 3 (by decide)) rep lab (fun i => pivots[i.val]!) (2,0) (by decide)
  · decide +kernel
  · apply Coefficients.injective_by_code rep code (fun i => codes[i.val]!)
    · decide +kernel
    · apply StrictMono.injective
      rw [Fin.strictMono_iff_lt_succ]
      decide +kernel
  · have hits : ∀ i : Fin 15, lab (pos (locations[i.val]! / 9)) (pos (locations[i.val]! % 9))=i := by decide +kernel
    exact fun i => ⟨_,_,hits i⟩
  all_goals decide +kernel

end C15

end SudokuNine
