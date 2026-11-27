import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case5707x378
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 439) := ⟨by decide⟩
private def W5707x378 (x:ZMod 439) : ℤ := ([0, 0, 36, 0, 72, 0, 36, 13, 35, 10, 36, 0, 72, 20, 49, 0, 71, 52, 46, 17, 72, 13, 36, 0, 35, 27, 56, 10, 12, 29, 36, 19, 34, 24, 15, 13, 9, 64, 53, 44, 35, 34, 49, 28, 72, 10, 36, 56, 71, 26, 63, 62, 19, 43, 46, 38, 48, 17, 65, 62, 72, 64, 55, 23, 70, 58, 60, 23, 51, 59, 49, 52, 45, 32, 27, 51, 16, 13, 7, 40, 71, 20, 70, 2, 12, 30, 64, 53, 35, 22, 46, 33, 72, 29, 19, 44, 34, 58, 62, 10, 26, 9, 25, 16, 55, 13, 6, 20, 9, 6, 1, 1, 11, 21, 53, 14, 28, 30, 25, 65, 35, 11, 27, 44, 18, 65, 59, 60, 33, 14, 21, 31, 23, 30, 59, 10, 14, 7, 22, 31, 12, 66, 15, 31, 8, 67, 68, 26, 63, 25, 14, 39, 52, 62, 49, 70, 43, 24, 3, 43, 34, 13, 56, 4, 33, 38, 38, 55, 48, 51, 66, 27, 27, 61, 16, 40, 71, 48, 58, 52, 9, 69, 69, 64, 35, 42, 65, 17, 55, 23, 7, 59, 70, 2, 21, 58, 25, 42, 46, 3, 62, 33, 45, 42, 61, 12, 52, 10, 18, 55, 49, 21, 42, 3, 56, 42, 45, 32, 42, 32, 37, 37, 37, 50, 47, 37, 57, 37, 16, 54, 50, 37, 64, 47, 66, 56, 61, 50, 28, 8, 71, 65, 47, 20, 63, 26, 7, 2, 54, 26, 28, 60, 22, 60, 23, 16, 69, 15, 50, 4, 57, 39, 67, 17, 59, 70, 66, 8, 22, 47, 46, 53, 50, 57, 43, 38, 58, 51, 67, 29, 48, 8, 29, 24, 51, 68, 67, 47, 44, 68, 30, 68, 31, 63, 62, 3, 26, 34, 61, 7, 50, 41, 2, 19, 15, 64, 25, 4, 12, 16, 33, 28, 6, 54, 60, 23, 39, 22, 6, 40, 70, 6, 49, 47, 19, 58, 40, 6, 69, 69, 1, 14, 1, 1, 18, 1, 11, 20, 14, 45, 29, 57, 63, 39, 63, 24, 24, 53, 52, 41, 3, 54, 34, 45, 11, 17, 21, 2, 15, 66, 45, 61, 32, 11, 32, 32, 27, 40, 71, 44, 5, 56, 28, 41, 53, 65, 18, 60, 59, 4, 43, 11, 22, 43, 33, 51, 38, 38, 57, 9, 21, 3, 61, 17, 5, 18, 9, 54, 39, 30, 25, 48, 69, 4, 8, 20, 5, 29, 24, 41, 48, 7, 15, 2, 46, 40, 54, 55, 18, 67, 12, 41, 57, 66, 5, 44, 39, 4, 19, 31, 5, 30, 8, 41, 68, 67, 5, 31, 68] : List ℤ).getD x.val 0
private def good5707x378 (n:ℕ) : Prop := let x:ZMod 439:=n; (73:ℤ)∣(if x=0 then (0:ℤ) else 1)+W5707x378 ((4:ZMod 439)*x)-W5707x378 x
private instance (n:ℕ) : Decidable (good5707x378 n) := by unfold good5707x378; infer_instance
private theorem good5707x378p0 : ∀i:Fin 32,good5707x378 (32*0+i.val) := by decide +kernel
private theorem good5707x378p1 : ∀i:Fin 32,good5707x378 (32*1+i.val) := by decide +kernel
private theorem good5707x378p2 : ∀i:Fin 32,good5707x378 (32*2+i.val) := by decide +kernel
private theorem good5707x378p3 : ∀i:Fin 32,good5707x378 (32*3+i.val) := by decide +kernel
private theorem good5707x378p4 : ∀i:Fin 32,good5707x378 (32*4+i.val) := by decide +kernel
private theorem good5707x378p5 : ∀i:Fin 32,good5707x378 (32*5+i.val) := by decide +kernel
private theorem good5707x378p6 : ∀i:Fin 32,good5707x378 (32*6+i.val) := by decide +kernel
private theorem good5707x378p7 : ∀i:Fin 32,good5707x378 (32*7+i.val) := by decide +kernel
private theorem good5707x378p8 : ∀i:Fin 32,good5707x378 (32*8+i.val) := by decide +kernel
private theorem good5707x378p9 : ∀i:Fin 32,good5707x378 (32*9+i.val) := by decide +kernel
private theorem good5707x378p10 : ∀i:Fin 32,good5707x378 (32*10+i.val) := by decide +kernel
private theorem good5707x378p11 : ∀i:Fin 32,good5707x378 (32*11+i.val) := by decide +kernel
private theorem good5707x378p12 : ∀i:Fin 32,good5707x378 (32*12+i.val) := by decide +kernel
private theorem good5707x378p13 : ∀i:Fin 32,good5707x378 (32*13+i.val) := by decide +kernel
private theorem W5707x378Levels : ∀x:ZMod 439,(73:ℤ)∣(if x=0 then (0:ℤ) else 1)+W5707x378 (443 • x)-W5707x378 x := by
  intro x; rw [nsmul_eq_mul,show ((443:ℕ):ZMod 439)=4 by decide]
  let a : Fin 14 := ⟨x.val/32,by have h:=x.val_lt; omega⟩
  let b : Fin 32 := ⟨x.val%32,Nat.mod_lt _ (by decide)⟩
  have done (z:Fin 14) : ∀i:Fin 32,good5707x378 (32*z.val+i.val) := by
    fin_cases z
    · exact good5707x378p0
    · exact good5707x378p1
    · exact good5707x378p2
    · exact good5707x378p3
    · exact good5707x378p4
    · exact good5707x378p5
    · exact good5707x378p6
    · exact good5707x378p7
    · exact good5707x378p8
    · exact good5707x378p9
    · exact good5707x378p10
    · exact good5707x378p11
    · exact good5707x378p12
    · exact good5707x378p13
  have e:=done a b
  have eq : 32*a.val+b.val=x.val := by simp [a,b,Nat.div_add_mod]
  rw [eq] at e
  simpa only [good5707x378,ZMod.natCast_zmod_val] using e

theorem fibre_5707_378 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=5707) :
    ¬∃f:G→ℤ,IsSDS 378 1 f := by
  apply long_prime_pair_transfer G 13 439 (by decide) hg
  exact long_local_exclusion 13 439 29 443 110 293 6 73 378 1 6 ⟨29,1,66,219⟩ ⟨29,0,66,219⟩
    (by decide) W5707x378 W5707x378Levels (by decide +kernel) 18 11 11 49 ⟨1,-1,0,0⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
#print axioms fibre_5707_378
end Case5707x378

end Signed39.Contraction
