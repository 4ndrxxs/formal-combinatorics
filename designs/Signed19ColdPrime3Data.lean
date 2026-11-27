import SignedDivisorSlice
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification
import SignedClassicalCases

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def qInputs_3_19 : ℕ → Option QuotientInput
  | 19 => some ⟨19,3,9,0,19⟩
  | 29 => some ⟨29,3,14,0,19⟩
  | 41 => some ⟨41,3,4,0,19⟩
  | 43 => some ⟨43,3,21,0,19⟩
  | 49 => some ⟨7,3,3,0,19⟩
  | 53 => some ⟨53,3,26,0,19⟩
  | 61 => some ⟨61,3,5,0,19⟩
  | 73 => some ⟨73,3,6,0,19⟩
  | 89 => some ⟨89,3,44,0,19⟩
  | 133 => some ⟨7,3,3,0,19⟩
  | 163 => some ⟨163,3,81,0,19⟩
  | 173 => some ⟨173,3,86,0,19⟩
  | 281 => some ⟨281,3,140,0,19⟩
  | 413 => some ⟨7,3,3,0,19⟩
  | 569 => some ⟨569,3,284,0,19⟩
  | 749 => some ⟨7,3,3,0,19⟩
  | 953 => some ⟨953,3,476,0,19⟩
  | _ => none

def keep_3_19 : List (ℕ × ℤ) := [(59,7),(59,112),(71,43),(71,64),(107,7),(107,232)]

end Signed39.Contraction
