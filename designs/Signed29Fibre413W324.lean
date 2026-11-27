import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case413x324
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
private def W413x324 (x:ZMod 59) : ℤ := ([0, 0, 0, 28, 22, 8, 28, 24, 22, 27, 8, 3, 21, 20, 24, 7, 15, 5, 27, 12, 1, 23, 25, 9, 21, 16, 13, 26, 17, 18, 7, 6, 15, 2, 5, 3, 20, 14, 12, 19, 1, 9, 23, 4, 25, 6, 2, 10, 14, 19, 16, 4, 13, 10, 26, 11, 17, 11, 18] : List ℤ).getD x.val 0
private theorem W413x324Levels : ∀x:ZMod 59,(29:ℤ)∣(if x=0 then (0:ℤ) else 1)+W413x324 (239 • x)-W413x324 x := by
  have done : ∀x:ZMod 59,(29:ℤ)∣(if x=0 then (0:ℤ) else 1)+W413x324 ((3:ZMod 59)*x)-W413x324 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((239:ℕ):ZMod 59)=3 by decide]; exact done x

theorem fibre_413_324 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=413) :
    ¬∃f:G→ℤ,IsSDS 324 121 f := by
  apply long_prime_pair_transfer G 7 59 (by decide) hg
  exact long_sign_exclusion 7 59 29 239 20 30 6 29 324 121 224 ⟨29,1,8,29⟩ ⟨29,0,8,29⟩
    (by decide) W413x324 W413x324Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_413_324
end Case413x324

end Signed39.Contraction
