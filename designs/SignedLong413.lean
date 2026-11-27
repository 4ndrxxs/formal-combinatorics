import SignedLongTransfer

namespace Signed39.Contraction
namespace Long413

set_option maxRecDepth 16384
set_option maxHeartbeats 7500000

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

private def w0 (x:ZMod 59) : ℤ := ([0, 0, 0, 3, 21, 5, 3, 15, 21, 6, 5, 20, 24, 27, 15, 8, 13, 14, 6, 22, 26, 18, 12, 2, 24, 10, 19, 9, 7, 4, 8, 11, 13, 23, 14, 20, 27, 16, 22, 1, 26, 2, 18, 17, 12, 11, 23, 28, 16, 1, 10, 17, 19, 28, 9, 25, 7, 25, 4] : List ℤ).getD x.val 0
private theorem w0_levels : ∀x:ZMod 59,(29:ℤ)∣(if x=0 then (0:ℤ) else 1)+w0 (407 • x)-w0 x := by decide +kernel

private theorem product_N47733 : ¬∃f:ZMod 7×ZMod 59→ℤ,IsSDS 29 1 f :=
  long_sign_exclusion 7 59 4 407 49 42 27 29 29 1 21 ⟨2,2,138,174⟩ ⟨2,0,138,174⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N47733 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=413) :
    ¬∃f:G→ℤ,IsSDS 29 1 f := long_prime_pair_transfer G 7 59 (by decide) h product_N47733

private theorem product_N47746 : ¬∃f:ZMod 7×ZMod 59→ℤ,IsSDS 116 4 f :=
  long_sign_exclusion 7 59 16 407 49 42 27 29 116 4 42 ⟨2,4,138,174⟩ ⟨2,0,138,174⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N47746 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=413) :
    ¬∃f:G→ℤ,IsSDS 116 4 f := long_prime_pair_transfer G 7 59 (by decide) h product_N47746

private theorem product_N47790 : ¬∃f:ZMod 7×ZMod 59→ℤ,IsSDS 232 57 f :=
  long_sign_exclusion 7 59 25 407 49 42 27 29 232 57 154 ⟨5,2,168,174⟩ ⟨5,0,168,174⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N47790 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=413) :
    ¬∃f:G→ℤ,IsSDS 232 57 f := long_prime_pair_transfer G 7 59 (by decide) h product_N47790

private theorem product_N47801 : ¬∃f:ZMod 7×ZMod 59→ℤ,IsSDS 261 9 f :=
  long_sign_exclusion 7 59 36 407 49 42 27 29 261 9 63 ⟨2,2,138,174⟩ ⟨3,2,48,174⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N47801 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=413) :
    ¬∃f:G→ℤ,IsSDS 261 9 f := long_prime_pair_transfer G 7 59 (by decide) h product_N47801

private theorem product_N47819 : ¬∃f:ZMod 7×ZMod 59→ℤ,IsSDS 289 86 f :=
  long_sign_exclusion 7 59 29 407 49 42 27 29 289 86 189 ⟨29,1,7,29⟩ ⟨29,0,7,29⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N47819 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=413) :
    ¬∃f:G→ℤ,IsSDS 289 86 f := long_prime_pair_transfer G 7 59 (by decide) h product_N47819

private theorem product_N47839 : ¬∃f:ZMod 7×ZMod 59→ℤ,IsSDS 324 121 f :=
  long_sign_exclusion 7 59 29 407 49 42 27 29 324 121 224 ⟨29,1,7,29⟩ ⟨29,0,7,29⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N47839 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=413) :
    ¬∃f:G→ℤ,IsSDS 324 121 f := long_prime_pair_transfer G 7 59 (by decide) h product_N47839

private theorem product_N47853 : ¬∃f:ZMod 7×ZMod 59→ℤ,IsSDS 337 162 f :=
  long_sign_exclusion 7 59 25 407 49 42 27 29 337 162 259 ⟨5,2,168,174⟩ ⟨5,0,168,174⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N47853 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=413) :
    ¬∃f:G→ℤ,IsSDS 337 162 f := long_prime_pair_transfer G 7 59 (by decide) h product_N47853

private theorem product_N47878 : ¬∃f:ZMod 7×ZMod 59→ℤ,IsSDS 372 1 f :=
  long_sign_exclusion 7 59 53 407 49 42 27 29 372 1 28 ⟨53,1,30,87⟩ ⟨53,0,30,87⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N47878 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=413) :
    ¬∃f:G→ℤ,IsSDS 372 1 f := long_prime_pair_transfer G 7 59 (by decide) h product_N47878

private theorem product_N47907 : ¬∃f:ZMod 7×ZMod 59→ℤ,IsSDS 400 372 f :=
  long_sign_exclusion 7 59 4 407 49 42 27 29 400 372 392 ⟨2,2,138,174⟩ ⟨2,0,138,174⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N47907 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=413) :
    ¬∃f:G→ℤ,IsSDS 400 372 f := long_prime_pair_transfer G 7 59 (by decide) h product_N47907

#print axioms case_N47733

end Long413
end Signed39.Contraction
