import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case1263x77
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 421) := ⟨by decide⟩
private def W1263x77 (x:ZMod 421) : ℤ := ([0, 0, 0, 52, 0, 48, 52, 77, 0, 104, 48, 38, 52, 15, 77, 100, 92, 22, 104, 73, 35, 24, 38, 32, 52, 83, 2, 51, 64, 82, 100, 43, 92, 90, 22, 7, 104, 85, 73, 67, 35, 62, 24, 69, 38, 47, 19, 1, 39, 36, 83, 74, 2, 65, 51, 86, 64, 20, 82, 87, 87, 93, 43, 76, 92, 50, 90, 80, 9, 84, 7, 101, 104, 75, 85, 30, 73, 10, 54, 13, 35, 103, 49, 63, 11, 57, 69, 29, 38, 4, 47, 79, 19, 95, 1, 16, 39, 44, 36, 37, 83, 81, 74, 58, 2, 59, 65, 77, 51, 100, 86, 32, 64, 56, 20, 67, 82, 14, 74, 86, 87, 76, 80, 9, 43, 26, 76, 42, 92, 16, 50, 71, 90, 45, 80, 99, 9, 42, 71, 99, 7, 53, 101, 53, 91, 25, 75, 88, 85, 55, 30, 40, 60, 21, 10, 91, 54, 31, 13, 12, 35, 96, 103, 62, 49, 33, 63, 88, 11, 17, 57, 72, 69, 89, 29, 55, 25, 34, 4, 30, 34, 28, 79, 40, 19, 28, 95, 60, 1, 23, 3, 8, 39, 66, 44, 102, 36, 5, 37, 78, 83, 27, 81, 54, 61, 97, 58, 31, 2, 6, 59, 13, 65, 48, 77, 12, 51, 15, 100, 22, 73, 24, 32, 96, 64, 82, 56, 103, 20, 85, 67, 62, 69, 47, 1, 49, 74, 65, 86, 20, 87, 93, 76, 50, 80, 84, 101, 75, 43, 10, 26, 11, 63, 70, 29, 4, 79, 3, 16, 57, 50, 81, 71, 72, 90, 8, 32, 56, 67, 14, 99, 89, 9, 26, 42, 16, 71, 45, 99, 42, 7, 53, 53, 25, 101, 68, 40, 21, 91, 31, 12, 96, 75, 33, 88, 17, 72, 89, 55, 34, 30, 41, 40, 28, 60, 23, 21, 66, 102, 5, 91, 27, 54, 97, 31, 6, 13, 48, 12, 15, 22, 24, 96, 95, 103, 98, 62, 47, 49, 78, 33, 93, 63, 84, 88, 10, 11, 70, 17, 3, 57, 81, 72, 8, 56, 14, 89, 26, 29, 45, 55, 66, 25, 68, 21, 44, 4, 33, 17, 102, 34, 41, 28, 23, 79, 18, 27, 5, 19, 61, 15, 37, 95, 98, 60, 78, 93, 84, 23, 70, 3, 94, 8, 14, 39, 45, 66, 68, 44, 46, 102, 41, 36, 18, 5, 61, 37, 98, 78, 97, 70, 94, 27, 58, 68, 46, 41, 18, 61, 98, 97, 94, 58, 46, 18, 6, 94, 46, 6, 59, 59] : List ℤ).getD x.val 0
private def good1263x77 (n:ℕ) : Prop := let x:ZMod 421:=n; (105:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1263x77 ((9:ZMod 421)*x)-W1263x77 x
private instance (n:ℕ) : Decidable (good1263x77 n) := by unfold good1263x77; infer_instance
private theorem good1263x77p0 : ∀i:Fin 32,good1263x77 (32*0+i.val) := by decide +kernel
private theorem good1263x77p1 : ∀i:Fin 32,good1263x77 (32*1+i.val) := by decide +kernel
private theorem good1263x77p2 : ∀i:Fin 32,good1263x77 (32*2+i.val) := by decide +kernel
private theorem good1263x77p3 : ∀i:Fin 32,good1263x77 (32*3+i.val) := by decide +kernel
private theorem good1263x77p4 : ∀i:Fin 32,good1263x77 (32*4+i.val) := by decide +kernel
private theorem good1263x77p5 : ∀i:Fin 32,good1263x77 (32*5+i.val) := by decide +kernel
private theorem good1263x77p6 : ∀i:Fin 32,good1263x77 (32*6+i.val) := by decide +kernel
private theorem good1263x77p7 : ∀i:Fin 32,good1263x77 (32*7+i.val) := by decide +kernel
private theorem good1263x77p8 : ∀i:Fin 32,good1263x77 (32*8+i.val) := by decide +kernel
private theorem good1263x77p9 : ∀i:Fin 32,good1263x77 (32*9+i.val) := by decide +kernel
private theorem good1263x77p10 : ∀i:Fin 32,good1263x77 (32*10+i.val) := by decide +kernel
private theorem good1263x77p11 : ∀i:Fin 32,good1263x77 (32*11+i.val) := by decide +kernel
private theorem good1263x77p12 : ∀i:Fin 32,good1263x77 (32*12+i.val) := by decide +kernel
private theorem good1263x77p13 : ∀i:Fin 32,good1263x77 (32*13+i.val) := by decide +kernel
private theorem W1263x77Levels : ∀x:ZMod 421,(105:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1263x77 (430 • x)-W1263x77 x := by
  intro x; rw [nsmul_eq_mul,show ((430:ℕ):ZMod 421)=9 by decide]
  let a : Fin 14 := ⟨x.val/32,by have h:=x.val_lt; omega⟩
  let b : Fin 32 := ⟨x.val%32,Nat.mod_lt _ (by decide)⟩
  have done (z:Fin 14) : ∀i:Fin 32,good1263x77 (32*z.val+i.val) := by
    fin_cases z
    · exact good1263x77p0
    · exact good1263x77p1
    · exact good1263x77p2
    · exact good1263x77p3
    · exact good1263x77p4
    · exact good1263x77p5
    · exact good1263x77p6
    · exact good1263x77p7
    · exact good1263x77p8
    · exact good1263x77p9
    · exact good1263x77p10
    · exact good1263x77p11
    · exact good1263x77p12
    · exact good1263x77p13
  have e:=done a b
  have eq : 32*a.val+b.val=x.val := by simp [a,b,Nat.div_add_mod]
  rw [eq] at e
  simpa only [good1263x77,ZMod.natCast_zmod_val] using e

theorem fibre_1263_77 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1263) :
    ¬∃f:G→ℤ,IsSDS 77 2 f := by
  apply long_prime_pair_transfer G 3 421 (by decide) hg
  exact long_sign_exclusion 3 421 25 430 234 158 2 105 77 2 51 ⟨5,2,86,210⟩ ⟨5,0,86,210⟩
    (by decide) W1263x77 W1263x77Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_1263_77
end Case1263x77

end Signed39.Contraction
