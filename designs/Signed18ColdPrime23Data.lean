import SignedDivisorSlice
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification
import SignedFullConjugacy

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def qInputs_23_18 : ℕ → Option QuotientInput
  | 25 => some ⟨5,2,2,0,207⟩
  | 27 => some ⟨3,2,1,0,207⟩
  | 35 => some ⟨5,2,2,0,207⟩
  | 37 => some ⟨37,23,6,0,18⟩
  | 41 => some ⟨41,23,5,0,18⟩
  | 45 => some ⟨3,2,1,0,207⟩
  | 53 => some ⟨53,23,2,0,18⟩
  | 59 => some ⟨59,2,29,0,207⟩
  | 61 => some ⟨61,23,10,0,18⟩
  | 63 => some ⟨3,2,1,0,207⟩
  | 73 => some ⟨73,23,18,0,18⟩
  | 75 => some ⟨3,2,1,0,207⟩
  | 81 => some ⟨3,2,1,0,207⟩
  | 123 => some ⟨3,2,1,0,207⟩
  | 125 => some ⟨5,2,2,0,207⟩
  | 135 => some ⟨3,2,1,0,207⟩
  | 163 => some ⟨163,23,9,0,18⟩
  | 175 => some ⟨5,2,2,0,207⟩
  | 177 => some ⟨3,2,1,0,207⟩
  | 183 => some ⟨3,2,1,0,207⟩
  | 189 => some ⟨3,2,1,0,207⟩
  | 205 => some ⟨5,2,2,0,207⟩
  | 369 => some ⟨3,2,1,0,207⟩
  | 395 => some ⟨5,2,2,0,207⟩
  | 405 => some ⟨3,2,1,0,207⟩
  | 413 => some ⟨59,2,29,0,207⟩
  | 449 => some ⟨449,23,56,0,18⟩
  | 531 => some ⟨3,2,1,0,207⟩
  | 549 => some ⟨3,2,1,0,207⟩
  | 557 => some ⟨557,2,278,0,207⟩
  | 573 => some ⟨3,2,1,0,207⟩
  | 587 => some ⟨587,2,293,0,207⟩
  | 615 => some ⟨3,2,1,0,207⟩
  | 947 => some ⟨947,2,473,0,207⟩
  | 1109 => some ⟨1109,2,554,0,207⟩
  | 1141 => some ⟨163,23,9,0,18⟩
  | 1239 => some ⟨3,2,1,0,207⟩
  | 1647 => some ⟨3,2,1,0,207⟩
  | 1719 => some ⟨3,2,1,0,207⟩
  | 1845 => some ⟨3,2,1,0,207⟩
  | 2245 => some ⟨5,2,2,0,207⟩
  | 2765 => some ⟨5,2,2,0,207⟩
  | 2935 => some ⟨5,2,2,0,207⟩
  | 3717 => some ⟨3,2,1,0,207⟩
  | 3869 => some ⟨53,23,2,0,18⟩
  | 5157 => some ⟨3,2,1,0,207⟩
  | 6629 => some ⟨947,2,473,0,207⟩
  | _ => none

def keep_23_18 : List (ℕ × ℤ) := [(49,270),(49,293),(79,35),(79,1346),(191,27),(191,3730),(553,5),(553,12218),(727,2)]

end Signed39.Contraction
