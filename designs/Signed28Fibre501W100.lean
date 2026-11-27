import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case501x100
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 167) := ⟨by decide⟩
private def W501x100 (x:ZMod 167) : ℤ := ([0, 0, 51, 41, 19, 0, 9, 55, 70, 82, 51, 44, 60, 18, 23, 41, 38, 58, 50, 20, 19, 13, 12, 71, 28, 15, 69, 40, 74, 46, 9, 11, 6, 2, 26, 55, 18, 35, 71, 59, 70, 56, 64, 64, 63, 82, 39, 77, 79, 27, 66, 16, 37, 63, 8, 44, 42, 61, 14, 10, 60, 80, 62, 54, 57, 33, 53, 68, 77, 29, 23, 81, 69, 79, 3, 56, 39, 16, 27, 65, 38, 81, 24, 66, 32, 73, 32, 4, 31, 76, 50, 73, 7, 52, 45, 20, 47, 72, 78, 43, 34, 4, 67, 8, 5, 13, 31, 26, 59, 48, 12, 76, 10, 42, 29, 3, 65, 17, 61, 30, 28, 5, 48, 14, 30, 15, 22, 36, 25, 22, 1, 52, 21, 75, 36, 40, 45, 58, 80, 25, 74, 35, 49, 62, 37, 46, 47, 68, 54, 1, 24, 72, 7, 57, 67, 11, 78, 17, 33, 21, 6, 43, 49, 53, 75, 2, 34] : List ℤ).getD x.val 0
private theorem W501x100Levels : ∀x:ZMod 167,(83:ℤ)∣(if x=0 then (0:ℤ) else 1)+W501x100 (343 • x)-W501x100 x := by
  have done : ∀x:ZMod 167,(83:ℤ)∣(if x=0 then (0:ℤ) else 1)+W501x100 ((9:ZMod 167)*x)-W501x100 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((343:ℕ):ZMod 167)=9 by decide]; exact done x

theorem fibre_501_100 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=501) :
    ¬∃f:G→ℤ,IsSDS 100 16 f := by
  apply long_prime_pair_transfer G 3 167 (by decide) hg
  exact long_sign_exclusion 3 167 28 343 130 21 2 83 100 16 90 ⟨2,2,96,166⟩ ⟨7,1,3,83⟩
    (by decide) W501x100 W501x100Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_501_100
end Case501x100

end Signed39.Contraction
