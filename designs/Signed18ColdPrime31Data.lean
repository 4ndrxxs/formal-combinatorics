import SignedDivisorSlice
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification
import SignedFullConjugacy

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def qInputs_31_18 : ℕ → Option QuotientInput
  | 37 => some ⟨37,31,2,0,18⟩
  | 39 => some ⟨3,2,1,0,279⟩
  | 41 => some ⟨41,31,5,0,18⟩
  | 53 => some ⟨53,2,26,0,279⟩
  | 57 => some ⟨3,2,1,0,279⟩
  | 59 => some ⟨59,2,29,0,279⟩
  | 61 => some ⟨61,2,30,0,279⟩
  | 67 => some ⟨67,2,33,0,279⟩
  | 69 => some ⟨3,2,1,0,279⟩
  | 87 => some ⟨3,2,1,0,279⟩
  | 107 => some ⟨107,2,53,0,279⟩
  | 111 => some ⟨3,2,1,0,279⟩
  | 117 => some ⟨3,2,1,0,279⟩
  | 123 => some ⟨3,2,1,0,279⟩
  | 171 => some ⟨3,2,1,0,279⟩
  | 183 => some ⟨3,2,1,0,279⟩
  | 227 => some ⟨227,2,113,0,279⟩
  | 233 => some ⟨233,31,58,0,18⟩
  | 247 => some ⟨13,31,2,0,18⟩
  | 261 => some ⟨3,2,1,0,279⟩
  | 277 => some ⟨277,2,46,0,279⟩
  | 549 => some ⟨3,2,1,0,279⟩
  | 557 => some ⟨557,2,278,0,279⟩
  | 741 => some ⟨3,2,1,0,279⟩
  | 757 => some ⟨757,2,378,0,279⟩
  | 773 => some ⟨773,2,386,0,279⟩
  | 831 => some ⟨3,2,1,0,279⟩
  | 1501 => some ⟨19,31,3,0,18⟩
  | 1541 => some ⟨67,2,33,0,279⟩
  | 1671 => some ⟨3,2,1,0,279⟩
  | 2223 => some ⟨3,2,1,0,279⟩
  | 2319 => some ⟨3,2,1,0,279⟩
  | 2493 => some ⟨3,2,1,0,279⟩
  | 3029 => some ⟨13,31,2,0,18⟩
  | 3733 => some ⟨3733,2,1866,0,279⟩
  | 3959 => some ⟨37,31,2,0,18⟩
  | 5013 => some ⟨3,2,1,0,279⟩
  | 5221 => some ⟨227,2,113,0,279⟩
  | 6957 => some ⟨3,2,1,0,279⟩
  | 8941 => some ⟨8941,31,298,0,18⟩
  | _ => none

def keep_31_18 : List (ℕ × ℤ) := [(79,19),(151,82),(151,3523),(239,2),(983,2)]

end Signed39.Contraction
