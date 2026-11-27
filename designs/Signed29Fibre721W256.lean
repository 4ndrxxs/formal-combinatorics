import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case721x256
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 103) := ⟨by decide⟩
private def W721x256 (x:ZMod 103) : ℤ := ([0, 0, 40, 0, 29, 35, 40, 50, 18, 6, 24, 20, 29, 33, 39, 41, 7, 8, 46, 31, 13, 50, 9, 45, 18, 25, 22, 6, 28, 4, 30, 21, 47, 26, 48, 34, 35, 12, 20, 33, 2, 13, 39, 16, 49, 41, 34, 14, 7, 49, 14, 8, 11, 11, 46, 10, 17, 31, 44, 1, 19, 42, 10, 5, 36, 17, 15, 32, 37, 45, 23, 44, 24, 27, 1, 25, 9, 19, 22, 21, 42, 12, 2, 16, 28, 43, 5, 4, 38, 36, 30, 32, 23, 27, 3, 15, 47, 43, 38, 26, 3, 37, 48] : List ℤ).getD x.val 0
private theorem W721x256Levels : ∀x:ZMod 103,(51:ℤ)∣(if x=0 then (0:ℤ) else 1)+W721x256 (316 • x)-W721x256 x := by
  have done : ∀x:ZMod 103,(51:ℤ)∣(if x=0 then (0:ℤ) else 1)+W721x256 ((7:ZMod 103)*x)-W721x256 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((316:ℕ):ZMod 103)=7 by decide]; exact done x

theorem fibre_721_256 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=721) :
    ¬∃f:G→ℤ,IsSDS 256 53 f := by
  apply long_prime_pair_transfer G 7 103 (by decide) hg
  exact long_sign_exclusion 7 103 29 316 59 86 1 51 256 53 196 ⟨29,1,38,51⟩ ⟨29,0,38,51⟩
    (by decide) W721x256 W721x256Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_721_256
end Case721x256

end Signed39.Contraction
