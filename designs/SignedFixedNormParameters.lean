import SignedArithmeticSieve

/-! Enumerations at fixed norms 21 and 56, parameterized by the cofactor of the group order. -/

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def list21 (m : ℕ) : Prop := m=7 ∨ m=17 ∨ m=25 ∨ m=35 ∨ m=37 ∨ m=41 ∨ m=101
instance (m : ℕ) : Decidable (list21 m) := by unfold list21; infer_instance

def list56 (m : ℕ) (l : ℤ) : Prop := m=11 ∨ m=13 ∨ m=25 ∨ m=43 ∨ m=55 ∨ m=61 ∨ m=67 ∨ m=335 ∨
  (m=31 ∧ (l=44 ∨ l=65)) ∨ (m=167 ∧ (l=1 ∨ l=1100))
instance (m : ℕ) (l : ℤ) : Decidable (list56 m l) := by unfold list56; infer_instance

theorem norm21_parameters : ∀ m : Fin 155, 3 < m.val → ¬2 ∣ m.val → ¬3 ∣ m.val → ∀ c : Fin 155,
    let l := (3*(c.val:ℤ)^2-7)/(m.val:ℤ)
    numericalParameter 3 m.val 7 c.val l → list21 m.val := by decide +kernel

private def valid56At (m : ℕ) : Prop := 7 < m → ¬2 ∣ m → ¬7 ∣ m → ∀ c : Fin 457,
    let l := (7*(c.val:ℤ)^2-8)/(m:ℤ)
    numericalParameter 7 m 8 c.val l → list56 m l
private instance (m:ℕ) : Decidable (valid56At m) := by unfold valid56At; infer_instance

private theorem norm56chunk0 : ∀j:Fin 16,(16*0+j.val)<457 → valid56At (16*0+j.val) := by decide +kernel
private theorem norm56chunk1 : ∀j:Fin 16,(16*1+j.val)<457 → valid56At (16*1+j.val) := by decide +kernel
private theorem norm56chunk2 : ∀j:Fin 16,(16*2+j.val)<457 → valid56At (16*2+j.val) := by decide +kernel
private theorem norm56chunk3 : ∀j:Fin 16,(16*3+j.val)<457 → valid56At (16*3+j.val) := by decide +kernel
private theorem norm56chunk4 : ∀j:Fin 16,(16*4+j.val)<457 → valid56At (16*4+j.val) := by decide +kernel
private theorem norm56chunk5 : ∀j:Fin 16,(16*5+j.val)<457 → valid56At (16*5+j.val) := by decide +kernel
private theorem norm56chunk6 : ∀j:Fin 16,(16*6+j.val)<457 → valid56At (16*6+j.val) := by decide +kernel
private theorem norm56chunk7 : ∀j:Fin 16,(16*7+j.val)<457 → valid56At (16*7+j.val) := by decide +kernel
private theorem norm56chunk8 : ∀j:Fin 16,(16*8+j.val)<457 → valid56At (16*8+j.val) := by decide +kernel
private theorem norm56chunk9 : ∀j:Fin 16,(16*9+j.val)<457 → valid56At (16*9+j.val) := by decide +kernel
private theorem norm56chunk10 : ∀j:Fin 16,(16*10+j.val)<457 → valid56At (16*10+j.val) := by decide +kernel
private theorem norm56chunk11 : ∀j:Fin 16,(16*11+j.val)<457 → valid56At (16*11+j.val) := by decide +kernel
private theorem norm56chunk12 : ∀j:Fin 16,(16*12+j.val)<457 → valid56At (16*12+j.val) := by decide +kernel
private theorem norm56chunk13 : ∀j:Fin 16,(16*13+j.val)<457 → valid56At (16*13+j.val) := by decide +kernel
private theorem norm56chunk14 : ∀j:Fin 16,(16*14+j.val)<457 → valid56At (16*14+j.val) := by decide +kernel
private theorem norm56chunk15 : ∀j:Fin 16,(16*15+j.val)<457 → valid56At (16*15+j.val) := by decide +kernel
private theorem norm56chunk16 : ∀j:Fin 16,(16*16+j.val)<457 → valid56At (16*16+j.val) := by decide +kernel
private theorem norm56chunk17 : ∀j:Fin 16,(16*17+j.val)<457 → valid56At (16*17+j.val) := by decide +kernel
private theorem norm56chunk18 : ∀j:Fin 16,(16*18+j.val)<457 → valid56At (16*18+j.val) := by decide +kernel
private theorem norm56chunk19 : ∀j:Fin 16,(16*19+j.val)<457 → valid56At (16*19+j.val) := by decide +kernel
private theorem norm56chunk20 : ∀j:Fin 16,(16*20+j.val)<457 → valid56At (16*20+j.val) := by decide +kernel
private theorem norm56chunk21 : ∀j:Fin 16,(16*21+j.val)<457 → valid56At (16*21+j.val) := by decide +kernel
private theorem norm56chunk22 : ∀j:Fin 16,(16*22+j.val)<457 → valid56At (16*22+j.val) := by decide +kernel
private theorem norm56chunk23 : ∀j:Fin 16,(16*23+j.val)<457 → valid56At (16*23+j.val) := by decide +kernel
private theorem norm56chunk24 : ∀j:Fin 16,(16*24+j.val)<457 → valid56At (16*24+j.val) := by decide +kernel
private theorem norm56chunk25 : ∀j:Fin 16,(16*25+j.val)<457 → valid56At (16*25+j.val) := by decide +kernel
private theorem norm56chunk26 : ∀j:Fin 16,(16*26+j.val)<457 → valid56At (16*26+j.val) := by decide +kernel
private theorem norm56chunk27 : ∀j:Fin 16,(16*27+j.val)<457 → valid56At (16*27+j.val) := by decide +kernel
private theorem norm56chunk28 : ∀j:Fin 16,(16*28+j.val)<457 → valid56At (16*28+j.val) := by decide +kernel

theorem norm56_parameters : ∀ m : Fin 457, 7 < m.val → ¬2 ∣ m.val → ¬7 ∣ m.val → ∀ c : Fin 457,
    let l := (7*(c.val:ℤ)^2-8)/(m.val:ℤ)
    numericalParameter 7 m.val 8 c.val l → list56 m.val l := by
  intro m
  let a : Fin 29 := ⟨m.val/16,by have h:=m.isLt; omega⟩
  let b : Fin 16 := ⟨m.val%16,Nat.mod_lt _ (by decide)⟩
  have cover (z:Fin 29) : ∀j:Fin 16,(16*z.val+j.val)<457 → valid56At (16*z.val+j.val) := by
    fin_cases z
    · exact norm56chunk0
    · exact norm56chunk1
    · exact norm56chunk2
    · exact norm56chunk3
    · exact norm56chunk4
    · exact norm56chunk5
    · exact norm56chunk6
    · exact norm56chunk7
    · exact norm56chunk8
    · exact norm56chunk9
    · exact norm56chunk10
    · exact norm56chunk11
    · exact norm56chunk12
    · exact norm56chunk13
    · exact norm56chunk14
    · exact norm56chunk15
    · exact norm56chunk16
    · exact norm56chunk17
    · exact norm56chunk18
    · exact norm56chunk19
    · exact norm56chunk20
    · exact norm56chunk21
    · exact norm56chunk22
    · exact norm56chunk23
    · exact norm56chunk24
    · exact norm56chunk25
    · exact norm56chunk26
    · exact norm56chunk27
    · exact norm56chunk28
  have eq : 16*a.val+b.val=m.val := by simp [a,b,Nat.div_add_mod]
  have done:=cover a b
  rw [eq] at done
  exact done m.isLt

end Signed39.Contraction

