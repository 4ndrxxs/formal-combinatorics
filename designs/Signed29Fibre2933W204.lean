import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case2933x204
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 419) := ⟨by decide⟩
private def W2933x204 (x:ZMod 419) : ℤ := ([0, 0, 0, 0, 0, 0, 0, 15, 0, 1, 0, 12, 0, 0, 15, 0, 0, 0, 1, 13, 0, 15, 12, 0, 0, 14, 8, 1, 15, 0, 0, 6, 0, 12, 17, 15, 1, 17, 13, 7, 0, 7, 15, 8, 12, 1, 0, 18, 16, 11, 14, 18, 6, 14, 1, 12, 15, 13, 0, 14, 4, 4, 4, 16, 4, 5, 12, 18, 17, 8, 15, 11, 1, 6, 17, 3, 13, 8, 7, 5, 3, 2, 7, 6, 15, 16, 8, 14, 12, 3, 1, 15, 2, 5, 18, 8, 16, 13, 11, 13, 16, 9, 18, 2, 6, 15, 18, 1, 17, 9, 12, 17, 15, 9, 17, 7, 1, 7, 14, 15, 4, 5, 4, 4, 4, 2, 16, 3, 4, 9, 5, 9, 12, 9, 1, 5, 2, 9, 8, 9, 15, 18, 11, 1, 5, 18, 14, 11, 17, 14, 3, 17, 16, 18, 8, 3, 7, 6, 13, 11, 3, 15, 2, 16, 11, 12, 10, 6, 15, 11, 1, 14, 5, 2, 3, 10, 12, 14, 6, 13, 4, 4, 4, 4, 10, 17, 5, 10, 18, 16, 10, 7, 18, 3, 13, 2, 11, 8, 13, 6, 5, 7, 10, 15, 18, 10, 2, 3, 10, 6, 15, 16, 18, 11, 1, 12, 17, 2, 11, 13, 12, 3, 17, 1, 15, 17, 12, 14, 17, 6, 7, 8, 1, 14, 7, 18, 14, 12, 13, 14, 4, 16, 5, 18, 4, 11, 4, 18, 8, 3, 2, 6, 16, 12, 3, 13, 5, 8, 9, 13, 9, 2, 17, 16, 9, 17, 9, 7, 9, 7, 5, 7, 2, 3, 9, 7, 9, 1, 9, 5, 15, 12, 18, 8, 11, 16, 18, 3, 5, 11, 18, 8, 12, 6, 11, 14, 17, 13, 14, 13, 4, 4, 17, 12, 16, 4, 3, 5, 8, 2, 7, 11, 7, 1, 6, 16, 11, 8, 13, 12, 3, 1, 15, 14, 6, 8, 14, 17, 11, 14, 16, 2, 10, 18, 3, 6, 12, 13, 11, 13, 1, 16, 17, 7, 5, 7, 2, 7, 1, 5, 10, 8, 16, 3, 14, 6, 6, 14, 13, 10, 4, 4, 4, 5, 2, 11, 1, 16, 8, 12, 17, 10, 5, 17, 10, 2, 18, 6, 16, 13, 18, 3, 7, 10, 7, 8, 3, 6, 14, 10, 2, 5, 11, 16, 8, 10, 13, 2, 6, 9, 3, 10, 8, 9, 10, 5, 15, 10, 2, 9, 10, 9, 2, 10, 11, 9, 10, 9, 6] : List ℤ).getD x.val 0
private def good2933x204 (n:ℕ) : Prop := let x:ZMod 419:=n; (19:ℤ)∣(if x=0 then (0:ℤ) else 1)+W2933x204 ((47:ZMod 419)*x)-W2933x204 x
private instance (n:ℕ) : Decidable (good2933x204 n) := by unfold good2933x204; infer_instance
private theorem good2933x204p0 : ∀i:Fin 32,good2933x204 (32*0+i.val) := by decide +kernel
private theorem good2933x204p1 : ∀i:Fin 32,good2933x204 (32*1+i.val) := by decide +kernel
private theorem good2933x204p2 : ∀i:Fin 32,good2933x204 (32*2+i.val) := by decide +kernel
private theorem good2933x204p3 : ∀i:Fin 32,good2933x204 (32*3+i.val) := by decide +kernel
private theorem good2933x204p4 : ∀i:Fin 32,good2933x204 (32*4+i.val) := by decide +kernel
private theorem good2933x204p5 : ∀i:Fin 32,good2933x204 (32*5+i.val) := by decide +kernel
private theorem good2933x204p6 : ∀i:Fin 32,good2933x204 (32*6+i.val) := by decide +kernel
private theorem good2933x204p7 : ∀i:Fin 32,good2933x204 (32*7+i.val) := by decide +kernel
private theorem good2933x204p8 : ∀i:Fin 32,good2933x204 (32*8+i.val) := by decide +kernel
private theorem good2933x204p9 : ∀i:Fin 32,good2933x204 (32*9+i.val) := by decide +kernel
private theorem good2933x204p10 : ∀i:Fin 32,good2933x204 (32*10+i.val) := by decide +kernel
private theorem good2933x204p11 : ∀i:Fin 32,good2933x204 (32*11+i.val) := by decide +kernel
private theorem good2933x204p12 : ∀i:Fin 32,good2933x204 (32*12+i.val) := by decide +kernel
private theorem good2933x204p13 : ∀i:Fin 32,good2933x204 (32*13+i.val) := by decide +kernel
private theorem W2933x204Levels : ∀x:ZMod 419,(19:ℤ)∣(if x=0 then (0:ℤ) else 1)+W2933x204 (1723 • x)-W2933x204 x := by
  intro x; rw [nsmul_eq_mul,show ((1723:ℕ):ZMod 419)=47 by decide]
  let a : Fin 14 := ⟨x.val/32,by have h:=x.val_lt; omega⟩
  let b : Fin 32 := ⟨x.val%32,Nat.mod_lt _ (by decide)⟩
  have done (z:Fin 14) : ∀i:Fin 32,good2933x204 (32*z.val+i.val) := by
    fin_cases z
    · exact good2933x204p0
    · exact good2933x204p1
    · exact good2933x204p2
    · exact good2933x204p3
    · exact good2933x204p4
    · exact good2933x204p5
    · exact good2933x204p6
    · exact good2933x204p7
    · exact good2933x204p8
    · exact good2933x204p9
    · exact good2933x204p10
    · exact good2933x204p11
    · exact good2933x204p12
    · exact good2933x204p13
  have e:=done a b
  have eq : 32*a.val+b.val=x.val := by simp [a,b,Nat.div_add_mod]
  rw [eq] at e
  simpa only [good2933x204,ZMod.natCast_zmod_val] using e

theorem fibre_2933_204 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=2933) :
    ¬∃f:G→ℤ,IsSDS 204 1 f := by
  apply long_prime_pair_transfer G 7 419 (by decide) hg
  exact long_sign_exclusion 7 419 29 1723 107 82 5 19 204 1 56 ⟨29,1,88,209⟩ ⟨29,0,88,209⟩
    (by decide) W2933x204 W2933x204Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_2933_204
end Case2933x204

end Signed39.Contraction
