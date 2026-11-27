import SignedLongTransfer

namespace Signed39.Contraction
namespace Long321

set_option maxRecDepth 16384
set_option maxHeartbeats 7500000

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 107) := ⟨by decide⟩

private def w0 (x:ZMod 107) : ℤ := ([0, 0, 0, 36, 51, 7, 36, 11, 51, 19, 5, 31, 34, 39, 9, 43, 49, 25, 19, 28, 5, 47, 31, 44, 34, 12, 39, 2, 9, 21, 41, 27, 49, 14, 23, 16, 17, 15, 28, 22, 3, 13, 45, 48, 29, 26, 44, 40, 32, 20, 12, 8, 37, 1, 2, 38, 7, 11, 21, 33, 41, 43, 25, 30, 47, 46, 14, 4, 23, 27, 16, 18, 17, 24, 15, 48, 26, 42, 22, 8, 3, 38, 13, 33, 45, 30, 46, 4, 29, 18, 24, 50, 42, 10, 40, 35, 32, 6, 20, 50, 10, 35, 6, 52, 37, 52, 1] : List ℤ).getD x.val 0
private theorem w0_levels : ∀x:ZMod 107,(53:ℤ)∣(if x=0 then (0:ℤ) else 1)+w0 (319 • x)-w0 x := by decide +kernel

private theorem product_N27756 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 64 7 f :=
  long_sign_exclusion 3 107 19 319 53 71 25 53 64 7 48 ⟨19,1,17,53⟩ ⟨19,0,17,53⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27756 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 64 7 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27756

private theorem product_N27763 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 100 25 f :=
  long_sign_exclusion 3 107 25 319 53 71 25 53 100 25 90 ⟨5,2,44,106⟩ ⟨5,0,44,106⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27763 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 100 25 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27763

private theorem product_N27777 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 145 34 f :=
  long_sign_exclusion 3 107 37 319 53 71 25 53 145 34 105 ⟨37,1,7,53⟩ ⟨37,0,7,53⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27777 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 145 34 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27777

private theorem product_N27797 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 196 13 f :=
  long_sign_exclusion 3 107 61 319 53 71 25 53 196 13 66 ⟨61,1,16,53⟩ ⟨61,0,16,53⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27797 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 196 13 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27797

private theorem product_N27799 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 196 40 f :=
  long_sign_exclusion 3 107 52 319 53 71 25 53 196 40 114 ⟨2,2,54,106⟩ ⟨13,1,19,53⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27799 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 196 40 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27799

private theorem product_N27800 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 196 49 f :=
  long_sign_exclusion 3 107 49 319 53 71 25 53 196 49 126 ⟨7,2,90,106⟩ ⟨7,0,90,106⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27800 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 196 49 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27800

private theorem product_N27816 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 241 4 f :=
  long_sign_exclusion 3 107 79 319 53 71 25 53 241 4 39 ⟨79,1,33,53⟩ ⟨79,0,33,53⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27816 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 241 4 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27816

private theorem product_N27821 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 241 166 f :=
  long_sign_exclusion 3 107 25 319 53 71 25 53 241 166 231 ⟨5,2,44,106⟩ ⟨5,0,44,106⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27821 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 241 166 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27821

private theorem product_N27831 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 256 28 f :=
  long_sign_exclusion 3 107 76 319 53 71 25 53 256 28 96 ⟨2,2,54,106⟩ ⟨19,1,17,53⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27831 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 256 28 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27831

private theorem product_N27834 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 256 64 f :=
  long_sign_exclusion 3 107 64 319 53 71 25 53 256 64 144 ⟨2,6,54,106⟩ ⟨2,0,54,106⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27834 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 256 64 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27834

private theorem product_N27837 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 256 145 f :=
  long_sign_exclusion 3 107 37 319 53 71 25 53 256 145 216 ⟨37,1,7,53⟩ ⟨37,0,7,53⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27837 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 256 145 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27837

private theorem product_N27847 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 265 118 f :=
  long_sign_exclusion 3 107 49 319 53 71 25 53 265 118 195 ⟨7,2,90,106⟩ ⟨7,0,90,106⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27847 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 265 118 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27847

private theorem product_N27859 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 289 97 f :=
  long_sign_exclusion 3 107 64 319 53 71 25 53 289 97 177 ⟨2,6,54,106⟩ ⟨2,0,54,106⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27859 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 289 97 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27859

private theorem product_N27860 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 289 133 f :=
  long_sign_exclusion 3 107 52 319 53 71 25 53 289 133 207 ⟨2,2,54,106⟩ ⟨13,1,19,53⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27860 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 289 133 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27860

private theorem product_N27861 : ¬∃f:ZMod 3×ZMod 107→ℤ,IsSDS 289 232 f :=
  long_sign_exclusion 3 107 19 319 53 71 25 53 289 232 273 ⟨19,1,17,53⟩ ⟨19,0,17,53⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N27861 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=321) :
    ¬∃f:G→ℤ,IsSDS 289 232 f := long_prime_pair_transfer G 3 107 (by decide) h product_N27861

#print axioms case_N27756

end Long321
end Signed39.Contraction
