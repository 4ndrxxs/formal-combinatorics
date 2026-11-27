import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case1561x204
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 223) := ⟨by decide⟩
private def W1561x204 (x:ZMod 223) : ℤ := ([0, 0, 18, 0, 36, 0, 18, 21, 17, 0, 18, 24, 36, 0, 2, 9, 35, 7, 18, 0, 36, 21, 5, 31, 17, 8, 18, 30, 20, 20, 27, 28, 16, 33, 25, 21, 36, 15, 18, 5, 17, 13, 2, 2, 23, 9, 12, 27, 35, 5, 26, 7, 36, 30, 11, 32, 1, 1, 1, 1, 8, 22, 9, 21, 34, 16, 14, 10, 6, 31, 2, 23, 17, 32, 33, 9, 36, 8, 23, 30, 35, 35, 31, 25, 20, 7, 20, 13, 4, 22, 27, 21, 30, 29, 8, 4, 16, 34, 23, 33, 7, 34, 25, 15, 17, 30, 11, 14, 29, 24, 13, 8, 19, 19, 19, 3, 19, 6, 19, 28, 26, 19, 3, 13, 27, 12, 2, 10, 15, 3, 34, 24, 32, 21, 28, 9, 24, 26, 12, 14, 20, 20, 4, 3, 35, 29, 13, 5, 14, 28, 27, 12, 17, 7, 26, 32, 4, 3, 11, 23, 16, 15, 16, 34, 12, 33, 6, 27, 1, 22, 25, 10, 1, 32, 31, 29, 22, 6, 3, 28, 8, 33, 2, 22, 11, 24, 10, 31, 26, 14, 22, 5, 34, 16, 15, 9, 4, 29, 14, 11, 25, 10, 15, 4, 6, 13, 33, 24, 35, 28, 11, 30, 29, 23, 32, 6, 10, 12, 5, 25, 31, 7, 26] : List ℤ).getD x.val 0
private theorem W1561x204Levels : ∀x:ZMod 223,(37:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1561x204 (673 • x)-W1561x204 x := by
  have done : ∀x:ZMod 223,(37:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1561x204 ((4:ZMod 223)*x)-W1561x204 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((673:ℕ):ZMod 223)=4 by decide]; exact done x

theorem fibre_1561_204 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1561) :
    ¬∃f:G→ℤ,IsSDS 204 1 f := by
  apply long_prime_pair_transfer G 7 223 (by decide) hg
  exact long_sign_exclusion 7 223 29 673 56 149 7 37 204 1 42 ⟨29,1,93,111⟩ ⟨29,0,93,111⟩
    (by decide) W1561x204 W1561x204Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_1561_204
end Case1561x204

end Signed39.Contraction
