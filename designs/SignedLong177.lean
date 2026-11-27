import SignedLongTransfer

namespace Signed39.Contraction
namespace Long177

set_option maxRecDepth 16384
set_option maxHeartbeats 7500000

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

private def w0 (x:ZMod 59) : ℤ := ([0, 0, 0, 8, 27, 23, 8, 11, 27, 16, 23, 5, 6, 14, 11, 2, 25, 18, 16, 20, 21, 19, 3, 15, 6, 17, 12, 24, 9, 1, 2, 10, 25, 13, 18, 5, 14, 4, 20, 22, 21, 15, 19, 26, 3, 10, 13, 7, 4, 22, 17, 26, 12, 7, 24, 28, 9, 28, 1] : List ℤ).getD x.val 0
private theorem w0_levels : ∀x:ZMod 59,(29:ℤ)∣(if x=0 then (0:ℤ) else 1)+w0 (175 • x)-w0 x := by decide +kernel

private theorem product_N7506 : ¬∃f:ZMod 3×ZMod 59→ℤ,IsSDS 49 1 f :=
  long_sign_exclusion 3 59 16 175 29 39 18 29 49 1 15 ⟨2,4,30,58⟩ ⟨2,0,30,58⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N7506 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=177) :
    ¬∃f:G→ℤ,IsSDS 49 1 f := long_prime_pair_transfer G 3 59 (by decide) h product_N7506

private theorem product_N7507 : ¬∃f:ZMod 3×ZMod 59→ℤ,IsSDS 64 7 f :=
  long_sign_exclusion 3 59 19 175 29 39 18 29 64 7 36 ⟨19,1,13,29⟩ ⟨19,0,13,29⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N7507 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=177) :
    ¬∃f:G→ℤ,IsSDS 64 7 f := long_prime_pair_transfer G 3 59 (by decide) h product_N7507

private theorem product_N7523 : ¬∃f:ZMod 3×ZMod 59→ℤ,IsSDS 97 22 f :=
  long_sign_exclusion 3 59 25 175 29 39 18 29 97 22 63 ⟨5,2,34,58⟩ ⟨5,0,34,58⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N7523 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=177) :
    ¬∃f:G→ℤ,IsSDS 97 22 f := long_prime_pair_transfer G 3 59 (by decide) h product_N7523

private theorem product_N7525 : ¬∃f:ZMod 3×ZMod 59→ℤ,IsSDS 100 16 f :=
  long_sign_exclusion 3 59 28 175 29 39 18 29 100 16 54 ⟨2,2,30,58⟩ ⟨7,1,21,29⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N7525 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=177) :
    ¬∃f:G→ℤ,IsSDS 100 16 f := long_prime_pair_transfer G 3 59 (by decide) h product_N7525

private theorem product_N7549 : ¬∃f:ZMod 3×ZMod 59→ℤ,IsSDS 148 1 f :=
  long_sign_exclusion 3 59 49 175 29 39 18 29 148 1 18 ⟨7,2,21,29⟩ ⟨7,0,21,29⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N7549 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=177) :
    ¬∃f:G→ℤ,IsSDS 148 1 f := long_prime_pair_transfer G 3 59 (by decide) h product_N7549

private theorem product_N7554 : ¬∃f:ZMod 3×ZMod 59→ℤ,IsSDS 148 73 f :=
  long_sign_exclusion 3 59 25 175 29 39 18 29 148 73 114 ⟨5,2,34,58⟩ ⟨5,0,34,58⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N7554 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=177) :
    ¬∃f:G→ℤ,IsSDS 148 73 f := long_prime_pair_transfer G 3 59 (by decide) h product_N7554

private theorem product_N7559 : ¬∃f:ZMod 3×ZMod 59→ℤ,IsSDS 169 85 f :=
  long_sign_exclusion 3 59 28 175 29 39 18 29 169 85 123 ⟨2,2,30,58⟩ ⟨7,1,21,29⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N7559 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=177) :
    ¬∃f:G→ℤ,IsSDS 169 85 f := long_prime_pair_transfer G 3 59 (by decide) h product_N7559

private theorem product_N7560 : ¬∃f:ZMod 3×ZMod 59→ℤ,IsSDS 169 112 f :=
  long_sign_exclusion 3 59 19 175 29 39 18 29 169 112 141 ⟨19,1,13,29⟩ ⟨19,0,13,29⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N7560 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=177) :
    ¬∃f:G→ℤ,IsSDS 169 112 f := long_prime_pair_transfer G 3 59 (by decide) h product_N7560

#print axioms case_N7506

end Long177
end Signed39.Contraction
