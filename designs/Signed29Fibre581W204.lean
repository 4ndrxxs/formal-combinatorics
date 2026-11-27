import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case581x204
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 83) := ⟨by decide⟩
private def W581x204 (x:ZMod 83) : ℤ := ([0, 0, 0, 40, 33, 19, 40, 9, 33, 39, 11, 27, 32, 24, 9, 18, 25, 22, 39, 21, 11, 8, 27, 6, 32, 30, 16, 38, 1, 34, 10, 12, 25, 26, 22, 28, 31, 2, 13, 23, 3, 4, 8, 7, 19, 17, 6, 35, 24, 18, 30, 21, 16, 14, 38, 5, 1, 20, 34, 28, 10, 23, 12, 7, 17, 35, 26, 29, 14, 5, 20, 36, 31, 15, 2, 29, 13, 36, 15, 37, 3, 37, 4] : List ℤ).getD x.val 0
private theorem W581x204Levels : ∀x:ZMod 83,(41:ℤ)∣(if x=0 then (0:ℤ) else 1)+W581x204 (169 • x)-W581x204 x := by
  have done : ∀x:ZMod 83,(41:ℤ)∣(if x=0 then (0:ℤ) else 1)+W581x204 ((3:ZMod 83)*x)-W581x204 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((169:ℕ):ZMod 83)=3 by decide]; exact done x

theorem fibre_581_204 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=581) :
    ¬∃f:G→ℤ,IsSDS 204 1 f := by
  apply long_prime_pair_transfer G 7 83 (by decide) hg
  exact long_sign_exclusion 7 83 29 169 28 42 9 41 204 1 28 ⟨29,1,6,41⟩ ⟨29,0,6,41⟩
    (by decide) W581x204 W581x204Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_581_204
end Case581x204

end Signed39.Contraction
