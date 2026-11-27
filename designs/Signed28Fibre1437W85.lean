import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case1437x85
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 479) := ⟨by decide⟩
private def W1437x85 (x:ZMod 479) : ℤ := ([0, 0, 119, 107, 238, 15, 226, 176, 118, 214, 134, 8, 106, 0, 56, 122, 237, 137, 94, 174, 14, 44, 127, 194, 225, 30, 119, 82, 175, 90, 2, 139, 117, 115, 17, 191, 213, 51, 54, 107, 133, 133, 163, 184, 7, 229, 74, 46, 105, 113, 149, 5, 238, 110, 201, 23, 55, 42, 209, 24, 121, 96, 19, 151, 236, 15, 234, 163, 136, 62, 71, 157, 93, 180, 170, 137, 173, 184, 226, 233, 13, 189, 13, 187, 43, 152, 64, 197, 126, 36, 109, 176, 193, 7, 165, 189, 224, 211, 232, 222, 29, 104, 124, 198, 118, 59, 229, 40, 81, 219, 142, 158, 174, 49, 161, 209, 89, 214, 143, 74, 1, 16, 215, 1, 138, 45, 31, 91, 116, 52, 134, 230, 114, 111, 43, 97, 16, 63, 181, 185, 190, 153, 37, 8, 212, 105, 60, 220, 50, 215, 17, 46, 53, 112, 64, 154, 106, 216, 113, 217, 132, 131, 69, 27, 132, 130, 67, 20, 162, 68, 32, 149, 183, 26, 77, 206, 6, 131, 155, 102, 228, 129, 56, 203, 73, 66, 126, 145, 45, 19, 69, 58, 104, 161, 91, 122, 112, 67, 102, 36, 148, 31, 223, 27, 4, 148, 78, 169, 237, 182, 178, 196, 109, 25, 159, 199, 200, 76, 99, 48, 22, 205, 38, 201, 54, 5, 168, 116, 41, 130, 89, 52, 208, 154, 94, 61, 23, 101, 193, 86, 120, 227, 135, 57, 95, 128, 120, 3, 18, 55, 164, 75, 150, 202, 210, 20, 235, 72, 171, 227, 14, 65, 110, 166, 233, 125, 230, 143, 162, 144, 216, 32, 135, 44, 182, 38, 61, 18, 65, 114, 70, 68, 33, 78, 156, 57, 127, 70, 92, 103, 224, 79, 179, 160, 100, 39, 169, 90, 95, 194, 136, 121, 165, 211, 172, 111, 231, 217, 183, 66, 34, 128, 225, 101, 96, 166, 232, 35, 97, 98, 12, 147, 11, 140, 188, 30, 146, 87, 12, 222, 10, 84, 186, 26, 139, 178, 42, 3, 187, 156, 151, 147, 29, 50, 63, 77, 145, 80, 196, 168, 86, 82, 125, 236, 11, 172, 35, 181, 221, 206, 108, 177, 9, 123, 175, 195, 83, 140, 192, 108, 185, 47, 6, 24, 25, 152, 164, 158, 138, 234, 188, 198, 177, 190, 223, 199, 41, 159, 210, 75, 2, 92, 231, 98, 186, 9, 221, 47, 155, 218, 28, 21, 150, 207, 103, 204, 146, 59, 123, 37, 28, 170, 197, 200, 49, 202, 117, 53, 62, 87, 58, 4, 76, 21, 228, 167, 144, 33, 39, 115, 79, 71, 80, 40, 195, 212, 218, 129, 167, 99, 141, 88, 85, 179, 157, 51, 81, 83, 173, 207, 124, 141, 48, 153, 235, 191, 160, 93, 10, 219, 208, 60, 171, 203, 88, 22, 34, 72, 213, 100, 180, 84, 142, 192, 220, 204, 73, 85, 205] : List ℤ).getD x.val 0
private def good1437x85 (n:ℕ) : Prop := let x:ZMod 479:=n; (239:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1437x85 ((4:ZMod 479)*x)-W1437x85 x
private instance (n:ℕ) : Decidable (good1437x85 n) := by unfold good1437x85; infer_instance
private theorem good1437x85p0 : ∀i:Fin 32,good1437x85 (32*0+i.val) := by decide +kernel
private theorem good1437x85p1 : ∀i:Fin 32,good1437x85 (32*1+i.val) := by decide +kernel
private theorem good1437x85p2 : ∀i:Fin 32,good1437x85 (32*2+i.val) := by decide +kernel
private theorem good1437x85p3 : ∀i:Fin 32,good1437x85 (32*3+i.val) := by decide +kernel
private theorem good1437x85p4 : ∀i:Fin 32,good1437x85 (32*4+i.val) := by decide +kernel
private theorem good1437x85p5 : ∀i:Fin 32,good1437x85 (32*5+i.val) := by decide +kernel
private theorem good1437x85p6 : ∀i:Fin 32,good1437x85 (32*6+i.val) := by decide +kernel
private theorem good1437x85p7 : ∀i:Fin 32,good1437x85 (32*7+i.val) := by decide +kernel
private theorem good1437x85p8 : ∀i:Fin 32,good1437x85 (32*8+i.val) := by decide +kernel
private theorem good1437x85p9 : ∀i:Fin 32,good1437x85 (32*9+i.val) := by decide +kernel
private theorem good1437x85p10 : ∀i:Fin 32,good1437x85 (32*10+i.val) := by decide +kernel
private theorem good1437x85p11 : ∀i:Fin 32,good1437x85 (32*11+i.val) := by decide +kernel
private theorem good1437x85p12 : ∀i:Fin 32,good1437x85 (32*12+i.val) := by decide +kernel
private theorem good1437x85p13 : ∀i:Fin 32,good1437x85 (32*13+i.val) := by decide +kernel
private theorem good1437x85p14 : ∀i:Fin 32,good1437x85 (32*14+i.val) := by decide +kernel
private theorem W1437x85Levels : ∀x:ZMod 479,(239:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1437x85 (4 • x)-W1437x85 x := by
  intro x; rw [nsmul_eq_mul,show ((4:ℕ):ZMod 479)=4 by decide]
  let a : Fin 15 := ⟨x.val/32,by have h:=x.val_lt; omega⟩
  let b : Fin 32 := ⟨x.val%32,Nat.mod_lt _ (by decide)⟩
  have done (z:Fin 15) : ∀i:Fin 32,good1437x85 (32*z.val+i.val) := by
    fin_cases z
    · exact good1437x85p0
    · exact good1437x85p1
    · exact good1437x85p2
    · exact good1437x85p3
    · exact good1437x85p4
    · exact good1437x85p5
    · exact good1437x85p6
    · exact good1437x85p7
    · exact good1437x85p8
    · exact good1437x85p9
    · exact good1437x85p10
    · exact good1437x85p11
    · exact good1437x85p12
    · exact good1437x85p13
    · exact good1437x85p14
  have e:=done a b
  have eq : 32*a.val+b.val=x.val := by simp [a,b,Nat.div_add_mod]
  rw [eq] at e
  simpa only [good1437x85,ZMod.natCast_zmod_val] using e

theorem fibre_1437_85 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1437) :
    ¬∃f:G→ℤ,IsSDS 85 1 f := by
  apply long_prime_pair_transfer G 3 479 (by decide) hg
  exact long_sign_exclusion 3 479 28 4 120 160 67 239 85 1 39 ⟨2,2,2,478⟩ ⟨7,1,129,239⟩
    (by decide) W1437x85 W1437x85Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_1437_85
end Case1437x85

end Signed39.Contraction
