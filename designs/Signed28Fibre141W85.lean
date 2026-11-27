import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case141x85
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 47) := ⟨by decide⟩
private def W141x85 (x:ZMod 47) : ℤ := ([0, 0, 11, 2, 22, 0, 13, 17, 10, 4, 11, 19, 1, 1, 5, 2, 21, 20, 15, 9, 22, 19, 7, 5, 12, 14, 12, 6, 16, 8, 13, 14, 9, 21, 8, 17, 3, 18, 20, 3, 10, 6, 7, 15, 18, 4, 16] : List ℤ).getD x.val 0
private theorem W141x85Levels : ∀x:ZMod 47,(23:ℤ)∣(if x=0 then (0:ℤ) else 1)+W141x85 (4 • x)-W141x85 x := by
  have done : ∀x:ZMod 47,(23:ℤ)∣(if x=0 then (0:ℤ) else 1)+W141x85 ((4:ZMod 47)*x)-W141x85 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((4:ℕ):ZMod 47)=4 by decide]; exact done x

theorem fibre_141_85 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=141) :
    ¬∃f:G→ℤ,IsSDS 85 1 f := by
  apply long_prime_pair_transfer G 3 47 (by decide) hg
  exact long_sign_exclusion 3 47 28 4 12 16 11 23 85 1 15 ⟨2,2,2,46⟩ ⟨7,1,4,23⟩
    (by decide) W141x85 W141x85Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_141_85
end Case141x85

end Signed39.Contraction
