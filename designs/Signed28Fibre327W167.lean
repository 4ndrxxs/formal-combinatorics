import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case327x167
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 109) := ⟨by decide⟩
private def W327x167 (x:ZMod 109) : ℤ := ([0, 0, 0, 0, 0, 7, 0, 1, 0, 0, 7, 0, 0, 0, 1, 7, 8, 6, 0, 8, 7, 1, 6, 2, 5, 5, 3, 5, 1, 2, 7, 0, 8, 3, 6, 8, 1, 4, 7, 6, 3, 1, 1, 7, 6, 3, 2, 3, 8, 2, 5, 6, 3, 5, 5, 1, 6, 4, 7, 3, 8, 4, 1, 6, 8, 4, 2, 8, 6, 2, 8, 3, 2, 4, 5, 1, 7, 4, 3, 5, 6, 5, 1, 8, 2, 4, 7, 3, 7, 2, 3, 7, 2, 4, 4, 2, 8, 4, 2, 8, 6, 4, 6, 1, 3, 4, 5, 5, 5] : List ℤ).getD x.val 0
private theorem W327x167Levels : ∀x:ZMod 109,(9:ℤ)∣(if x=0 then (0:ℤ) else 1)+W327x167 (16 • x)-W327x167 x := by
  have done : ∀x:ZMod 109,(9:ℤ)∣(if x=0 then (0:ℤ) else 1)+W327x167 ((16:ZMod 109)*x)-W327x167 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((16:ℕ):ZMod 109)=16 by decide]; exact done x

theorem fibre_327_167 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=327) :
    ¬∃f:G→ℤ,IsSDS 167 83 f := by
  apply long_prime_pair_transfer G 3 109 (by decide) hg
  exact long_sign_exclusion 3 109 28 16 75 80 21 9 167 83 165 ⟨2,2,4,36⟩ ⟨7,1,3,27⟩
    (by decide) W327x167 W327x167Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_327_167
end Case327x167

end Signed39.Contraction
