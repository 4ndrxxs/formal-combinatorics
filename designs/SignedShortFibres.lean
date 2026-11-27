import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case203x178
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 29) := ⟨by decide⟩
private def W203x178 (x:ZMod 29) : ℤ := ([0, 0, 0, 2, 0, 3, 2, 6, 0, 4, 3, 5, 2, 1, 6, 5, 2, 3, 4, 4, 5, 1, 5, 3, 4, 1, 1, 6, 6] : List ℤ).getD x.val 0
private theorem W203x178Levels : ∀x:ZMod 29,(7:ℤ)∣(if x=0 then (0:ℤ) else 1)+W203x178 (36 • x)-W203x178 x := by
  have done : ∀x:ZMod 29,(7:ℤ)∣(if x=0 then (0:ℤ) else 1)+W203x178 ((7:ZMod 29)*x)-W203x178 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((36:ℕ):ZMod 29)=7 by decide]; exact done x

theorem fibre_203_178 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=203) :
    ¬∃f:G→ℤ,IsSDS 178 3 f := by
  apply long_prime_pair_transfer G 7 29 (by decide) hg
  exact long_sign_exclusion 7 29 25 36 25 5 1 7 178 3 28 ⟨5,2,12,42⟩ ⟨5,0,12,42⟩
    (by decide) W203x178 W203x178Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_203_178
end Case203x178

section Case329x289
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 47) := ⟨by decide⟩
private def W329x289 (x:ZMod 47) : ℤ := ([0, 0, 15, 9, 7, 0, 1, 19, 22, 18, 15, 5, 16, 16, 11, 9, 14, 21, 10, 6, 7, 5, 20, 11, 8, 17, 8, 4, 3, 13, 1, 17, 6, 14, 13, 19, 2, 12, 21, 2, 22, 4, 20, 10, 12, 18, 3] : List ℤ).getD x.val 0
private theorem W329x289Levels : ∀x:ZMod 47,(23:ℤ)∣(if x=0 then (0:ℤ) else 1)+W329x289 (8 • x)-W329x289 x := by
  have done : ∀x:ZMod 47,(23:ℤ)∣(if x=0 then (0:ℤ) else 1)+W329x289 ((8:ZMod 47)*x)-W329x289 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((8:ℕ):ZMod 47)=8 by decide]; exact done x

theorem fibre_329_289 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=329) :
    ¬∃f:G→ℤ,IsSDS 289 65 f := by
  apply long_prime_pair_transfer G 7 47 (by decide) hg
  exact long_sign_exclusion 7 47 32 8 6 27 6 23 289 65 147 ⟨2,5,3,69⟩ ⟨2,0,3,69⟩
    (by decide) W329x289 W329x289Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_329_289
end Case329x289

section Case329x305
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 47) := ⟨by decide⟩
private def W329x305 (x:ZMod 47) : ℤ := ([0, 0, 15, 9, 7, 0, 1, 19, 22, 18, 15, 5, 16, 16, 11, 9, 14, 21, 10, 6, 7, 5, 20, 11, 8, 17, 8, 4, 3, 13, 1, 17, 6, 14, 13, 19, 2, 12, 21, 2, 22, 4, 20, 10, 12, 18, 3] : List ℤ).getD x.val 0
private theorem W329x305Levels : ∀x:ZMod 47,(23:ℤ)∣(if x=0 then (0:ℤ) else 1)+W329x305 (8 • x)-W329x305 x := by
  have done : ∀x:ZMod 47,(23:ℤ)∣(if x=0 then (0:ℤ) else 1)+W329x305 ((8:ZMod 47)*x)-W329x305 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((8:ℕ):ZMod 47)=8 by decide]; exact done x

theorem fibre_329_305 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=329) :
    ¬∃f:G→ℤ,IsSDS 305 53 f := by
  apply long_prime_pair_transfer G 7 47 (by decide) hg
  exact long_sign_exclusion 7 47 36 8 6 27 6 23 305 53 133 ⟨2,2,3,69⟩ ⟨3,2,120,138⟩
    (by decide) W329x305 W329x305Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_329_305
end Case329x305

end Signed39.Contraction
