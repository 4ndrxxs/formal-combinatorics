import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case1807x1369
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 139) := ⟨by decide⟩
private def W1807x1369 (x:ZMod 139) : ℤ := ([0, 0, 0, 0, 0, 16, 8, 19, 0, 0, 16, 12, 8, 13, 19, 1, 18, 6, 8, 18, 11, 4, 20, 21, 8, 4, 21, 13, 14, 22, 1, 7, 3, 2, 14, 7, 16, 5, 18, 3, 19, 9, 4, 2, 5, 9, 16, 15, 8, 10, 12, 6, 6, 11, 8, 21, 22, 3, 7, 10, 1, 20, 7, 12, 11, 22, 20, 17, 14, 6, 15, 15, 16, 19, 5, 17, 18, 1, 21, 18, 4, 21, 9, 13, 4, 7, 2, 12, 5, 3, 9, 2, 1, 15, 15, 11, 3, 13, 18, 10, 20, 4, 14, 22, 6, 20, 19, 17, 16, 10, 21, 13, 7, 12, 3, 17, 15, 11, 5, 10, 19, 22, 20, 17, 2, 13, 12, 9, 11, 10, 22, 17, 5, 14, 2, 9, 14, 1, 6] : List ℤ).getD x.val 0
private theorem W1807x1369Levels : ∀x:ZMod 139,(23:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1807x1369 (482 • x)-W1807x1369 x := by
  have done : ∀x:ZMod 139,(23:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1807x1369 ((65:ZMod 139)*x)-W1807x1369 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((482:ℕ):ZMod 139)=65 by decide]; exact done x

theorem fibre_1807_1369 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1807) :
    ¬∃f:G→ℤ,IsSDS 1369 992 f := by
  apply long_prime_pair_transfer G 13 139 (by decide) hg
  exact long_sign_exclusion 13 139 29 482 77 63 39 23 1369 992 1339 ⟨29,1,6,69⟩ ⟨29,0,6,69⟩
    (by decide) W1807x1369 W1807x1369Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_1807_1369
end Case1807x1369

end Signed39.Contraction
