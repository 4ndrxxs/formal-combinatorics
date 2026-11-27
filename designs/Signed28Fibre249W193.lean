import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case249x193
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 83) := ⟨by decide⟩
private def W249x193 (x:ZMod 83) : ℤ := ([0, 0, 0, 5, 40, 28, 5, 37, 40, 10, 27, 29, 4, 3, 37, 33, 39, 13, 10, 18, 27, 1, 29, 11, 4, 14, 2, 15, 36, 35, 32, 22, 39, 34, 13, 24, 9, 31, 17, 8, 26, 21, 1, 6, 28, 38, 11, 30, 3, 33, 14, 18, 2, 12, 15, 16, 36, 23, 35, 24, 32, 8, 22, 6, 38, 30, 34, 19, 12, 16, 23, 25, 9, 7, 31, 19, 17, 25, 7, 20, 26, 20, 21] : List ℤ).getD x.val 0
private theorem W249x193Levels : ∀x:ZMod 83,(41:ℤ)∣(if x=0 then (0:ℤ) else 1)+W249x193 (4 • x)-W249x193 x := by
  have done : ∀x:ZMod 83,(41:ℤ)∣(if x=0 then (0:ℤ) else 1)+W249x193 ((4:ZMod 83)*x)-W249x193 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((4:ℕ):ZMod 83)=4 by decide]; exact done x

theorem fibre_249_193 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=249) :
    ¬∃f:G→ℤ,IsSDS 193 109 f := by
  apply long_prime_pair_transfer G 3 83 (by decide) hg
  exact long_sign_exclusion 3 83 28 4 21 28 8 41 193 109 165 ⟨2,2,2,82⟩ ⟨7,1,31,41⟩
    (by decide) W249x193 W249x193Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_249_193
end Case249x193

end Signed39.Contraction
