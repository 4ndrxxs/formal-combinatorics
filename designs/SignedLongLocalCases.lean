import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 17000
set_option maxHeartbeats 12000000

section Case327

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 109) := ⟨by decide⟩

private def W327 (x:ZMod 109) : ℤ := ([0, 0, 0, 0, 0, 8, 0, 5, 0, 0, 8, 0, 0, 0, 5, 8, 4, 3, 0, 4, 8, 5, 3, 1, 7, 7, 6, 7, 5, 1, 8, 0, 4, 6, 3, 4, 5, 2, 8, 3, 6, 5, 5, 8, 3, 6, 1, 6, 4, 1, 7, 3, 6, 7, 7, 5, 3, 2, 8, 6, 4, 2, 5, 3, 4, 2, 1, 4, 3, 1, 4, 6, 1, 2, 7, 5, 8, 2, 6, 7, 3, 7, 5, 4, 1, 2, 8, 6, 8, 1, 6, 8, 1, 2, 2, 1, 4, 2, 1, 4, 3, 2, 3, 5, 6, 2, 7, 7, 7] : List ℤ).getD x.val 0
private theorem levels327 : ∀x:ZMod 109,(9:ℤ)∣(if x=0 then (0:ℤ) else 1)+W327 (256 • x)-W327 x := by
  have h : ∀x:ZMod 109,(9:ℤ)∣(if x=0 then (0:ℤ) else 1)+W327 ((38:ZMod 109)*x)-W327 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((256:ℕ):ZMod 109)=38 by decide]; exact h x

theorem local_327_164 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=327) :
    ¬∃f:G→ℤ,IsSDS 164 80 f := by
  apply long_prime_pair_transfer G 3 109 (by decide) hg
  exact long_local_exclusion 3 109 28 256 66 56 15 9 164 80 54 ⟨2,2,8,36⟩ ⟨7,1,6,27⟩
    (by decide) W327 levels327 (by decide +kernel) 7 0 2 37 ⟨-2970,108,1,-1⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms local_327_164

end Case327

section Case2353

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 181) := ⟨by decide⟩

private def W2353 (x:ZMod 181) : ℤ := ([0, 0, 0, 0, 0, 4, 0, 0, 2, 0, 4, 5, 0, 12, 1, 4, 3, 0, 0, 10, 4, 0, 7, 10, 2, 8, 12, 2, 1, 7, 4, 1, 3, 5, 10, 4, 0, 11, 11, 12, 6, 13, 3, 6, 8, 4, 10, 13, 5, 14, 8, 9, 12, 14, 2, 9, 1, 10, 7, 9, 4, 13, 2, 8, 3, 1, 7, 2, 10, 12, 5, 3, 10, 11, 13, 8, 11, 6, 12, 1, 7, 2, 1, 10, 3, 4, 6, 7, 8, 6, 4, 12, 5, 1, 13, 14, 5, 2, 9, 5, 8, 13, 10, 5, 14, 4, 14, 5, 2, 11, 11, 11, 11, 3, 13, 14, 7, 14, 9, 8, 6, 13, 13, 6, 2, 12, 3, 1, 13, 6, 1, 7, 10, 9, 12, 6, 10, 14, 12, 7, 5, 13, 3, 2, 5, 11, 11, 1, 14, 11, 8, 12, 11, 9, 6, 5, 12, 9, 3, 14, 7, 13, 2, 8, 1, 9, 10, 7, 3, 9, 14, 3, 6, 9, 7, 8, 8, 9, 6, 14, 4] : List ℤ).getD x.val 0
private theorem levels2353 : ∀x:ZMod 181,(15:ℤ)∣(if x=0 then (0:ℤ) else 1)+W2353 (2289 • x)-W2353 x := by
  have h : ∀x:ZMod 181,(15:ℤ)∣(if x=0 then (0:ℤ) else 1)+W2353 ((117:ZMod 181)*x)-W2353 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((2289:ℕ):ZMod 181)=117 by decide]; exact h x

theorem local_2353_352 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=2353) :
    ¬∃f:G→ℤ,IsSDS 352 1 f := by
  apply long_prime_pair_transfer G 13 181 (by decide) hg
  exact long_local_exclusion 13 181 27 2289 82 142 39 15 352 1 4 ⟨3,3,21,45⟩ ⟨3,0,21,45⟩
    (by decide) W2353 levels2353 (by decide +kernel) 18 7 7 29 ⟨0,-11,1,0⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms local_2353_352

end Case2353

end Signed39.Contraction
