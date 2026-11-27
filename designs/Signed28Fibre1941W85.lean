import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case1941x85
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 647) := ⟨by decide⟩
private def W1941x85 (x:ZMod 647) : ℤ := ([0, 0, 109, 322, 218, 0, 108, 132, 4, 321, 109, 259, 217, 183, 241, 322, 113, 254, 107, 268, 218, 131, 45, 280, 3, 30, 292, 320, 27, 261, 108, 87, 222, 258, 40, 132, 216, 161, 54, 182, 4, 208, 240, 95, 154, 321, 66, 18, 112, 264, 139, 253, 78, 57, 106, 289, 136, 267, 47, 143, 217, 37, 196, 130, 8, 183, 44, 171, 149, 279, 241, 314, 2, 111, 270, 29, 163, 68, 291, 10, 113, 319, 317, 250, 26, 254, 204, 260, 263, 179, 107, 315, 175, 86, 127, 298, 221, 90, 50, 257, 248, 85, 39, 138, 187, 131, 166, 230, 215, 24, 75, 160, 245, 302, 53, 310, 156, 181, 252, 63, 3, 225, 146, 207, 305, 30, 239, 202, 117, 94, 292, 297, 153, 77, 280, 320, 258, 54, 65, 82, 27, 17, 100, 119, 111, 261, 220, 263, 56, 20, 138, 185, 272, 252, 177, 87, 77, 65, 119, 56, 222, 89, 105, 105, 103, 288, 36, 236, 135, 43, 40, 266, 313, 103, 46, 162, 49, 142, 288, 61, 216, 173, 101, 36, 284, 191, 195, 190, 236, 129, 84, 286, 7, 135, 199, 182, 159, 122, 43, 125, 34, 170, 194, 70, 148, 208, 247, 278, 296, 234, 240, 227, 275, 313, 16, 95, 1, 219, 133, 110, 184, 114, 269, 46, 31, 28, 88, 41, 162, 5, 96, 67, 265, 79, 290, 48, 38, 9, 172, 242, 112, 164, 11, 318, 255, 264, 316, 128, 91, 249, 139, 167, 25, 246, 311, 253, 226, 306, 203, 293, 78, 259, 83, 101, 262, 57, 186, 178, 66, 223, 106, 37, 44, 314, 163, 289, 174, 285, 191, 85, 136, 160, 126, 195, 209, 297, 228, 17, 220, 185, 47, 89, 6, 266, 49, 173, 165, 256, 129, 140, 247, 227, 294, 84, 58, 67, 38, 164, 286, 137, 196, 229, 186, 7, 174, 130, 228, 59, 165, 197, 8, 229, 198, 199, 214, 213, 214, 23, 212, 150, 74, 213, 145, 159, 22, 171, 244, 211, 152, 301, 149, 23, 52, 73, 99, 309, 212, 232, 155, 144, 271, 180, 158, 34, 251, 21, 74, 62, 170, 205, 2, 243, 282, 224, 210, 141, 145, 151, 70, 206, 300, 189, 304, 148, 299, 29, 22, 121, 238, 51, 193, 201, 72, 277, 116, 98, 244, 93, 308, 188, 291, 211, 268, 296, 231, 10, 152, 154, 234, 76, 143, 301, 279, 270, 303, 319, 179, 127, 257, 157, 317, 53, 33, 275, 64, 250, 82, 81, 20, 177, 26, 73, 13, 16, 61, 284, 99, 169, 125, 118, 204, 309, 110, 1, 5, 260, 242, 255, 219, 281, 293, 262, 223, 133, 55, 209, 155, 19, 140, 58, 137, 144, 197, 184, 150, 315, 271, 69, 114, 251, 205, 180, 176, 299, 51, 86, 188, 231, 76, 303, 157, 64, 147, 31, 118, 298, 281, 55, 28, 120, 221, 21, 273, 88, 120, 90, 104, 237, 41, 104, 50, 62, 102, 192, 237, 287, 200, 123, 35, 71, 248, 235, 276, 96, 134, 115, 32, 42, 97, 80, 39, 243, 12, 265, 92, 168, 312, 307, 79, 102, 187, 224, 45, 290, 192, 161, 210, 18, 48, 267, 166, 141, 295, 68, 287, 230, 175, 60, 9, 200, 215, 151, 146, 172, 153, 24, 100, 233, 272, 35, 75, 206, 283, 142, 71, 190, 300, 122, 194, 278, 245, 189, 269, 11, 235, 302, 304, 128, 318, 276, 83, 178, 14, 285, 126, 310, 6, 256, 294, 134, 156, 59, 198, 316, 115, 181, 52, 232, 158, 32, 282, 121, 274, 91, 42, 63, 238, 124, 249, 97, 33, 81, 13, 169, 80, 225, 193, 19, 167, 69, 176, 201, 147, 25, 273, 207, 72, 123, 246, 12, 305, 277, 15, 311, 295, 60, 116, 233, 283, 92, 239, 98, 14, 226, 168, 202, 274, 124, 306, 312, 117, 93, 15, 203, 307, 94, 308] : List ℤ).getD x.val 0
private def good1941x85 (n:ℕ) : Prop := let x:ZMod 647:=n; (323:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1941x85 ((3:ZMod 647)*x)-W1941x85 x
private instance (n:ℕ) : Decidable (good1941x85 n) := by unfold good1941x85; infer_instance
private theorem good1941x85p0 : ∀i:Fin 32,good1941x85 (32*0+i.val) := by decide +kernel
private theorem good1941x85p1 : ∀i:Fin 32,good1941x85 (32*1+i.val) := by decide +kernel
private theorem good1941x85p2 : ∀i:Fin 32,good1941x85 (32*2+i.val) := by decide +kernel
private theorem good1941x85p3 : ∀i:Fin 32,good1941x85 (32*3+i.val) := by decide +kernel
private theorem good1941x85p4 : ∀i:Fin 32,good1941x85 (32*4+i.val) := by decide +kernel
private theorem good1941x85p5 : ∀i:Fin 32,good1941x85 (32*5+i.val) := by decide +kernel
private theorem good1941x85p6 : ∀i:Fin 32,good1941x85 (32*6+i.val) := by decide +kernel
private theorem good1941x85p7 : ∀i:Fin 32,good1941x85 (32*7+i.val) := by decide +kernel
private theorem good1941x85p8 : ∀i:Fin 32,good1941x85 (32*8+i.val) := by decide +kernel
private theorem good1941x85p9 : ∀i:Fin 32,good1941x85 (32*9+i.val) := by decide +kernel
private theorem good1941x85p10 : ∀i:Fin 32,good1941x85 (32*10+i.val) := by decide +kernel
private theorem good1941x85p11 : ∀i:Fin 32,good1941x85 (32*11+i.val) := by decide +kernel
private theorem good1941x85p12 : ∀i:Fin 32,good1941x85 (32*12+i.val) := by decide +kernel
private theorem good1941x85p13 : ∀i:Fin 32,good1941x85 (32*13+i.val) := by decide +kernel
private theorem good1941x85p14 : ∀i:Fin 32,good1941x85 (32*14+i.val) := by decide +kernel
private theorem good1941x85p15 : ∀i:Fin 32,good1941x85 (32*15+i.val) := by decide +kernel
private theorem good1941x85p16 : ∀i:Fin 32,good1941x85 (32*16+i.val) := by decide +kernel
private theorem good1941x85p17 : ∀i:Fin 32,good1941x85 (32*17+i.val) := by decide +kernel
private theorem good1941x85p18 : ∀i:Fin 32,good1941x85 (32*18+i.val) := by decide +kernel
private theorem good1941x85p19 : ∀i:Fin 32,good1941x85 (32*19+i.val) := by decide +kernel
private theorem good1941x85p20 : ∀i:Fin 32,good1941x85 (32*20+i.val) := by decide +kernel
private theorem W1941x85Levels : ∀x:ZMod 647,(323:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1941x85 (1297 • x)-W1941x85 x := by
  intro x; rw [nsmul_eq_mul,show ((1297:ℕ):ZMod 647)=3 by decide]
  let a : Fin 21 := ⟨x.val/32,by have h:=x.val_lt; omega⟩
  let b : Fin 32 := ⟨x.val%32,Nat.mod_lt _ (by decide)⟩
  have done (z:Fin 21) : ∀i:Fin 32,good1941x85 (32*z.val+i.val) := by
    fin_cases z
    · exact good1941x85p0
    · exact good1941x85p1
    · exact good1941x85p2
    · exact good1941x85p3
    · exact good1941x85p4
    · exact good1941x85p5
    · exact good1941x85p6
    · exact good1941x85p7
    · exact good1941x85p8
    · exact good1941x85p9
    · exact good1941x85p10
    · exact good1941x85p11
    · exact good1941x85p12
    · exact good1941x85p13
    · exact good1941x85p14
    · exact good1941x85p15
    · exact good1941x85p16
    · exact good1941x85p17
    · exact good1941x85p18
    · exact good1941x85p19
    · exact good1941x85p20
  have e:=done a b
  have eq : 32*a.val+b.val=x.val := by simp [a,b,Nat.div_add_mod]
  rw [eq] at e
  simpa only [good1941x85,ZMod.natCast_zmod_val] using e

theorem fibre_1941_85 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1941) :
    ¬∃f:G→ℤ,IsSDS 85 1 f := by
  apply long_prime_pair_transfer G 3 647 (by decide) hg
  exact long_sign_exclusion 3 647 28 1297 216 324 1 323 85 1 45 ⟨2,2,80,646⟩ ⟨7,1,115,323⟩
    (by decide) W1941x85 W1941x85Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_1941_85
end Case1941x85

end Signed39.Contraction
