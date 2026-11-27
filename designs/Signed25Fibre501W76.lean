import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case501x76
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 167) := ⟨by decide⟩
private def W501x76 (x:ZMod 167) : ℤ := ([0, 0, 19, 82, 38, 0, 18, 27, 57, 81, 19, 5, 37, 36, 46, 82, 76, 33, 17, 40, 38, 26, 24, 59, 56, 30, 55, 80, 65, 9, 18, 22, 12, 4, 52, 27, 36, 70, 59, 35, 57, 29, 45, 45, 43, 81, 78, 71, 75, 54, 49, 32, 74, 43, 16, 5, 1, 39, 28, 20, 37, 77, 41, 25, 31, 66, 23, 53, 71, 58, 46, 79, 55, 75, 6, 29, 78, 32, 54, 47, 76, 79, 48, 49, 64, 63, 64, 8, 62, 69, 17, 63, 14, 21, 7, 40, 11, 61, 73, 3, 68, 8, 51, 16, 10, 26, 62, 52, 35, 13, 24, 69, 20, 1, 58, 6, 47, 34, 39, 60, 56, 10, 13, 28, 60, 30, 44, 72, 50, 44, 2, 21, 42, 67, 72, 80, 7, 33, 77, 50, 65, 70, 15, 41, 74, 9, 11, 53, 25, 2, 48, 61, 14, 31, 51, 22, 73, 34, 66, 42, 12, 3, 15, 23, 67, 4, 68] : List ℤ).getD x.val 0
private theorem W501x76Levels : ∀x:ZMod 167,(83:ℤ)∣(if x=0 then (0:ℤ) else 1)+W501x76 (337 • x)-W501x76 x := by
  have done : ∀x:ZMod 167,(83:ℤ)∣(if x=0 then (0:ℤ) else 1)+W501x76 ((3:ZMod 167)*x)-W501x76 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((337:ℕ):ZMod 167)=3 by decide]; exact done x

theorem fibre_501_76 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=501) :
    ¬∃f:G→ℤ,IsSDS 76 1 f := by
  apply long_prime_pair_transfer G 3 167 (by decide) hg
  exact long_sign_exclusion 3 167 25 337 56 84 1 83 76 1 24 ⟨5,2,94,166⟩ ⟨5,0,94,166⟩
    (by decide) W501x76 W501x76Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_501_76
end Case501x76

end Signed39.Contraction
