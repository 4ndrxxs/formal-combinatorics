import Quantum.Hadamard.PaleyTWord

/-! An explicit periodic complementary system over four signed coordinates. -/
namespace Hadamard.PeriodicT
namespace T271Skew
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : ℕ := 37955779988578097242161265546701994522434711357745665803218745423251848617103231391985797421799969444184756304209514798656940277300113244959100626168266963807832379259125626653321401465209685549209840066815217111108455158924777976180211774005192

private theorem part0 : Word.verify packed 271 0 16=true := by decide +kernel
private theorem part1 : Word.verify packed 271 16 16=true := by decide +kernel
private theorem part2 : Word.verify packed 271 32 16=true := by decide +kernel
private theorem part3 : Word.verify packed 271 48 16=true := by decide +kernel
private theorem part4 : Word.verify packed 271 64 16=true := by decide +kernel
private theorem part5 : Word.verify packed 271 80 16=true := by decide +kernel
private theorem part6 : Word.verify packed 271 96 16=true := by decide +kernel
private theorem part7 : Word.verify packed 271 112 16=true := by decide +kernel
private theorem part8 : Word.verify packed 271 128 16=true := by decide +kernel
private theorem part9 : Word.verify packed 271 144 16=true := by decide +kernel
private theorem part10 : Word.verify packed 271 160 16=true := by decide +kernel
private theorem part11 : Word.verify packed 271 176 16=true := by decide +kernel
private theorem part12 : Word.verify packed 271 192 16=true := by decide +kernel
private theorem part13 : Word.verify packed 271 208 16=true := by decide +kernel
private theorem part14 : Word.verify packed 271 224 16=true := by decide +kernel
private theorem part15 : Word.verify packed 271 240 16=true := by decide +kernel
private theorem part16 : Word.verify packed 271 256 15=true := by decide +kernel

private theorem checked (s : Fin 271) : Word.dot packed 271 s.val 271=if s.val=0 then 271 else 0 := by
  by_cases h0 : s.val<16
  · exact Word.verified part0 (by omega) (by omega)
  by_cases h1 : s.val<32
  · exact Word.verified part1 (by omega) (by omega)
  by_cases h2 : s.val<48
  · exact Word.verified part2 (by omega) (by omega)
  by_cases h3 : s.val<64
  · exact Word.verified part3 (by omega) (by omega)
  by_cases h4 : s.val<80
  · exact Word.verified part4 (by omega) (by omega)
  by_cases h5 : s.val<96
  · exact Word.verified part5 (by omega) (by omega)
  by_cases h6 : s.val<112
  · exact Word.verified part6 (by omega) (by omega)
  by_cases h7 : s.val<128
  · exact Word.verified part7 (by omega) (by omega)
  by_cases h8 : s.val<144
  · exact Word.verified part8 (by omega) (by omega)
  by_cases h9 : s.val<160
  · exact Word.verified part9 (by omega) (by omega)
  by_cases h10 : s.val<176
  · exact Word.verified part10 (by omega) (by omega)
  by_cases h11 : s.val<192
  · exact Word.verified part11 (by omega) (by omega)
  by_cases h12 : s.val<208
  · exact Word.verified part12 (by omega) (by omega)
  by_cases h13 : s.val<224
  · exact Word.verified part13 (by omega) (by omega)
  by_cases h14 : s.val<240
  · exact Word.verified part14 (by omega) (by omega)
  by_cases h15 : s.val<256
  · exact Word.verified part15 (by omega) (by omega)
  exact Word.verified part16 (by omega) (by omega)

def witness : System 271 := Word.system packed checked
theorem exists_system : Nonempty (System 271) := ⟨witness⟩
/-- The signed projection onto (1,-1,-1,-1) is a skew binary sequence. -/
def projection (j : Fin 271) : ℤ :=
  witness.entry 0 j - witness.entry 1 j - witness.entry 2 j - witness.entry 3 j

theorem skew_projection : projection 0 = 1 ∧
    ∀ j : Fin 271, j ≠ 0 → projection (-j) = - projection j := by decide +kernel

#print axioms exists_system
#print axioms skew_projection
end T271Skew
end Hadamard.PeriodicT
