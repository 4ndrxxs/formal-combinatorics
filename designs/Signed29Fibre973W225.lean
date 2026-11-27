import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case973x225
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 139) := ⟨by decide⟩
private def W973x225 (x:ZMod 139) : ℤ := ([0, 0, 0, 13, 11, 59, 24, 68, 11, 37, 59, 4, 24, 7, 68, 3, 22, 31, 37, 54, 1, 12, 4, 5, 35, 49, 7, 50, 10, 34, 14, 32, 22, 17, 42, 58, 48, 26, 65, 20, 1, 38, 23, 6, 15, 27, 16, 56, 35, 67, 49, 55, 18, 46, 61, 63, 10, 9, 34, 41, 14, 60, 32, 36, 33, 66, 28, 19, 42, 29, 58, 13, 48, 57, 26, 62, 65, 3, 31, 54, 12, 5, 38, 50, 23, 21, 17, 47, 15, 20, 27, 6, 16, 45, 56, 44, 46, 52, 67, 41, 60, 25, 55, 8, 18, 2, 57, 62, 61, 43, 63, 39, 21, 47, 9, 64, 45, 44, 52, 30, 25, 8, 2, 51, 43, 39, 36, 64, 33, 30, 66, 51, 28, 53, 19, 40, 53, 40, 29] : List ℤ).getD x.val 0
private theorem W973x225Levels : ∀x:ZMod 139,(69:ℤ)∣(if x=0 then (0:ℤ) else 1)+W973x225 (841 • x)-W973x225 x := by
  have done : ∀x:ZMod 139,(69:ℤ)∣(if x=0 then (0:ℤ) else 1)+W973x225 ((7:ZMod 139)*x)-W973x225 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((841:ℕ):ZMod 139)=7 by decide]; exact done x

theorem fibre_973_225 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=973) :
    ¬∃f:G→ℤ,IsSDS 225 22 f := by
  apply long_prime_pair_transfer G 7 139 (by decide) hg
  exact long_sign_exclusion 7 139 29 841 20 116 1 69 225 22 147 ⟨29,1,2,69⟩ ⟨29,0,2,69⟩
    (by decide) W973x225 W973x225Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_973_225
end Case973x225

end Signed39.Contraction
