import SignedDivisorSlice
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification
import SignedFullConjugacy

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def qInputs_7_18 : ℕ → Option QuotientInput
  | 25 => some ⟨5,2,2,0,63⟩
  | 33 => some ⟨3,2,1,0,63⟩
  | 39 => some ⟨3,2,1,0,63⟩
  | 43 => some ⟨43,7,3,0,18⟩
  | 45 => some ⟨3,2,1,0,63⟩
  | 55 => some ⟨5,2,2,0,63⟩
  | 61 => some ⟨61,2,30,0,63⟩
  | 65 => some ⟨5,2,2,0,63⟩
  | 67 => some ⟨67,2,33,0,63⟩
  | 75 => some ⟨3,2,1,0,63⟩
  | 93 => some ⟨3,2,1,0,63⟩
  | 99 => some ⟨3,2,1,0,63⟩
  | 107 => some ⟨107,2,53,0,63⟩
  | 117 => some ⟨3,2,1,0,63⟩
  | 125 => some ⟨5,2,2,0,63⟩
  | 157 => some ⟨157,2,26,0,63⟩
  | 165 => some ⟨3,2,1,0,63⟩
  | 173 => some ⟨173,2,86,0,63⟩
  | 183 => some ⟨3,2,1,0,63⟩
  | 193 => some ⟨193,7,12,0,18⟩
  | 215 => some ⟨5,2,2,0,63⟩
  | 225 => some ⟨3,2,1,0,63⟩
  | 233 => some ⟨233,7,58,0,18⟩
  | 325 => some ⟨5,2,2,0,63⟩
  | 341 => some ⟨11,2,5,0,63⟩
  | 375 => some ⟨3,2,1,0,63⟩
  | 401 => some ⟨401,2,100,0,63⟩
  | 495 => some ⟨3,2,1,0,63⟩
  | 519 => some ⟨3,2,1,0,63⟩
  | 549 => some ⟨3,2,1,0,63⟩
  | 677 => some ⟨677,2,338,0,63⟩
  | 829 => some ⟨829,7,138,0,18⟩
  | 1125 => some ⟨3,2,1,0,63⟩
  | 1165 => some ⟨5,2,2,0,63⟩
  | 1557 => some ⟨3,2,1,0,63⟩
  | 2005 => some ⟨5,2,2,0,63⟩
  | _ => none

def keep_7_18 : List (ℕ × ℤ) := [(31,22),(47,2),(887,2),(887,5987)]

end Signed39.Contraction
