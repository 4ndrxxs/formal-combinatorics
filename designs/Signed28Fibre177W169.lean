import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case177x169
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
private def W177x169 (x:ZMod 59) : ℤ := ([0, 0, 0, 4, 28, 26, 4, 20, 28, 8, 26, 17, 3, 7, 20, 1, 27, 9, 8, 10, 25, 24, 16, 22, 3, 23, 6, 12, 19, 15, 1, 5, 27, 21, 9, 17, 7, 2, 10, 11, 25, 22, 24, 13, 16, 5, 21, 18, 2, 11, 23, 13, 6, 18, 12, 14, 19, 14, 15] : List ℤ).getD x.val 0
private theorem W177x169Levels : ∀x:ZMod 59,(29:ℤ)∣(if x=0 then (0:ℤ) else 1)+W177x169 (4 • x)-W177x169 x := by
  have done : ∀x:ZMod 59,(29:ℤ)∣(if x=0 then (0:ℤ) else 1)+W177x169 ((4:ZMod 59)*x)-W177x169 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((4:ℕ):ZMod 59)=4 by decide]; exact done x

theorem fibre_177_169 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=177) :
    ¬∃f:G→ℤ,IsSDS 169 85 f := by
  apply long_prime_pair_transfer G 3 59 (by decide) hg
  exact long_sign_exclusion 3 59 28 4 15 20 7 29 169 85 123 ⟨2,2,2,58⟩ ⟨7,1,13,29⟩
    (by decide) W177x169 W177x169Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_177_169
end Case177x169

end Signed39.Contraction
