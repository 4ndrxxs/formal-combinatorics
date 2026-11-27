import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case7849x6832
local instance : Fact (Nat.Prime 47) := ⟨by decide⟩
local instance : Fact (Nat.Prime 167) := ⟨by decide⟩
private def W7849x6832 (x:ZMod 167) : ℤ := ([0, 0, 25, 38, 50, 0, 63, 53, 75, 76, 25, 59, 5, 43, 78, 38, 17, 74, 18, 57, 50, 8, 1, 82, 30, 22, 68, 31, 20, 73, 63, 77, 42, 14, 16, 53, 43, 79, 82, 81, 75, 60, 33, 33, 26, 76, 24, 41, 55, 23, 47, 29, 10, 26, 56, 59, 45, 12, 15, 70, 5, 62, 19, 46, 67, 65, 39, 61, 41, 37, 78, 69, 68, 55, 21, 60, 24, 29, 23, 40, 17, 69, 2, 47, 58, 13, 58, 28, 51, 34, 18, 13, 49, 32, 66, 57, 80, 6, 48, 52, 72, 28, 54, 56, 35, 8, 51, 16, 81, 4, 1, 34, 70, 45, 37, 21, 40, 36, 12, 44, 30, 35, 4, 15, 44, 22, 71, 3, 9, 71, 7, 32, 64, 27, 3, 31, 66, 74, 62, 9, 20, 79, 11, 19, 10, 73, 80, 61, 46, 7, 2, 6, 49, 67, 54, 77, 48, 36, 65, 64, 42, 52, 11, 39, 27, 14, 72] : List ℤ).getD x.val 0
private theorem W7849x6832Levels : ∀x:ZMod 167,(83:ℤ)∣(if x=0 then (0:ℤ) else 1)+W7849x6832 (706 • x)-W7849x6832 x := by
  have done : ∀x:ZMod 167,(83:ℤ)∣(if x=0 then (0:ℤ) else 1)+W7849x6832 ((38:ZMod 167)*x)-W7849x6832 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((706:ℕ):ZMod 167)=38 by decide]; exact done x

theorem fibre_7849_6832 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=7849) :
    ¬∃f:G→ℤ,IsSDS 6832 5516 f := by
  apply long_prime_pair_transfer G 47 167 (by decide) hg
  exact long_sign_exclusion 47 167 28 706 22 158 2 83 6832 5516 6580 ⟨2,2,322,1909⟩ ⟨7,1,368,1909⟩
    (by decide) W7849x6832 W7849x6832Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_7849_6832
end Case7849x6832

end Signed39.Contraction
