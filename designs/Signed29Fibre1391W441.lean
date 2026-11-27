import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case1391x441
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 107) := ⟨by decide⟩
private def W1391x441 (x:ZMod 107) : ℤ := ([0, 0, 0, 22, 40, 19, 22, 45, 40, 44, 6, 16, 9, 15, 32, 41, 27, 30, 44, 23, 6, 14, 16, 21, 9, 25, 15, 13, 32, 4, 28, 43, 27, 38, 17, 51, 31, 18, 23, 37, 46, 5, 1, 47, 3, 10, 21, 48, 49, 24, 25, 52, 2, 33, 13, 35, 19, 45, 4, 29, 28, 41, 30, 36, 14, 34, 38, 26, 17, 43, 51, 11, 31, 50, 18, 47, 10, 8, 37, 52, 46, 35, 5, 29, 1, 36, 34, 26, 3, 11, 50, 7, 8, 12, 48, 42, 49, 39, 24, 7, 12, 42, 39, 20, 2, 20, 33] : List ℤ).getD x.val 0
private theorem W1391x441Levels : ∀x:ZMod 107,(53:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1391x441 (79 • x)-W1391x441 x := by
  have done : ∀x:ZMod 107,(53:ℤ)∣(if x=0 then (0:ℤ) else 1)+W1391x441 ((79:ZMod 107)*x)-W1391x441 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((79:ℕ):ZMod 107)=79 by decide]; exact done x

theorem fibre_1391_441 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1391) :
    ¬∃f:G→ℤ,IsSDS 441 64 f := by
  apply long_prime_pair_transfer G 13 107 (by decide) hg
  exact long_sign_exclusion 13 107 29 79 42 59 7 53 441 64 299 ⟨29,1,66,159⟩ ⟨29,0,66,159⟩
    (by decide) W1391x441 W1391x441Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_1391_441
end Case1391x441

end Signed39.Contraction
