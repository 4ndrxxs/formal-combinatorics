import Quantum.Hadamard.PaleyTWord

/-! An explicit periodic complementary system over four signed coordinates. -/
namespace Hadamard.PeriodicT
namespace T331
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def packed : ℕ := 29954996420819730658912861646048170290813296778397037571742057555379016754634709634266213862395514405847230923314153366319336175915774536657891986482585874313454631813241494606620367387667820624583752011276155356688013716308819008098725952642446205773158830938890936000562266765569561103751513045224

private theorem part0 : Word.verify packed 331 0 16=true := by decide +kernel
private theorem part1 : Word.verify packed 331 16 16=true := by decide +kernel
private theorem part2 : Word.verify packed 331 32 16=true := by decide +kernel
private theorem part3 : Word.verify packed 331 48 16=true := by decide +kernel
private theorem part4 : Word.verify packed 331 64 16=true := by decide +kernel
private theorem part5 : Word.verify packed 331 80 16=true := by decide +kernel
private theorem part6 : Word.verify packed 331 96 16=true := by decide +kernel
private theorem part7 : Word.verify packed 331 112 16=true := by decide +kernel
private theorem part8 : Word.verify packed 331 128 16=true := by decide +kernel
private theorem part9 : Word.verify packed 331 144 16=true := by decide +kernel
private theorem part10 : Word.verify packed 331 160 16=true := by decide +kernel
private theorem part11 : Word.verify packed 331 176 16=true := by decide +kernel
private theorem part12 : Word.verify packed 331 192 16=true := by decide +kernel
private theorem part13 : Word.verify packed 331 208 16=true := by decide +kernel
private theorem part14 : Word.verify packed 331 224 16=true := by decide +kernel
private theorem part15 : Word.verify packed 331 240 16=true := by decide +kernel
private theorem part16 : Word.verify packed 331 256 16=true := by decide +kernel
private theorem part17 : Word.verify packed 331 272 16=true := by decide +kernel
private theorem part18 : Word.verify packed 331 288 16=true := by decide +kernel
private theorem part19 : Word.verify packed 331 304 16=true := by decide +kernel
private theorem part20 : Word.verify packed 331 320 11=true := by decide +kernel

private theorem checked (s : Fin 331) : Word.dot packed 331 s.val 331=if s.val=0 then 331 else 0 := by
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
  by_cases h16 : s.val<272
  · exact Word.verified part16 (by omega) (by omega)
  by_cases h17 : s.val<288
  · exact Word.verified part17 (by omega) (by omega)
  by_cases h18 : s.val<304
  · exact Word.verified part18 (by omega) (by omega)
  by_cases h19 : s.val<320
  · exact Word.verified part19 (by omega) (by omega)
  exact Word.verified part20 (by omega) (by omega)

def witness : System 331 := Word.system packed checked
theorem exists_system : Nonempty (System 331) := ⟨witness⟩
#print axioms exists_system
end T331
end Hadamard.PeriodicT
