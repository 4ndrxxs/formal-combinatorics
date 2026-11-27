import SignedDivisorSlice
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def qInputs_11_20 : ℕ → Option QuotientInput
  | 27 => some ⟨3,5,1,0,44⟩
  | 39 => some ⟨3,5,1,0,44⟩
  | 45 => some ⟨3,5,1,0,44⟩
  | 47 => some ⟨47,5,23,0,44⟩
  | 51 => some ⟨3,5,1,0,44⟩
  | 57 => some ⟨3,5,1,0,44⟩
  | 65 => some ⟨13,5,2,0,44⟩
  | 67 => some ⟨67,5,11,0,44⟩
  | 69 => some ⟨3,5,1,0,44⟩
  | 73 => some ⟨73,5,36,0,44⟩
  | 81 => some ⟨3,5,1,0,44⟩
  | 85 => some ⟨17,5,8,0,44⟩
  | 89 => some ⟨89,11,11,0,20⟩
  | 103 => some ⟨103,5,51,0,44⟩
  | 117 => some ⟨3,5,1,0,44⟩
  | 135 => some ⟨3,5,1,0,44⟩
  | 171 => some ⟨3,5,1,0,44⟩
  | 173 => some ⟨173,5,86,0,44⟩
  | 219 => some ⟨3,5,1,0,44⟩
  | 221 => some ⟨13,5,2,0,44⟩
  | 233 => some ⟨233,5,116,0,44⟩
  | 243 => some ⟨3,5,1,0,44⟩
  | 255 => some ⟨3,5,1,0,44⟩
  | 267 => some ⟨3,5,1,0,44⟩
  | 351 => some ⟨3,5,1,0,44⟩
  | 365 => some ⟨73,5,36,0,44⟩
  | 391 => some ⟨17,5,8,0,44⟩
  | 437 => some ⟨23,5,11,0,44⟩
  | 443 => some ⟨443,5,221,0,44⟩
  | 519 => some ⟨3,5,1,0,44⟩
  | 613 => some ⟨613,5,306,0,44⟩
  | 699 => some ⟨3,5,1,0,44⟩
  | 871 => some ⟨13,5,2,0,44⟩
  | 1053 => some ⟨3,5,1,0,44⟩
  | 1095 => some ⟨3,5,1,0,44⟩
  | 1311 => some ⟨3,5,1,0,44⟩
  | 1317 => some ⟨3,5,1,0,44⟩
  | 1839 => some ⟨3,5,1,0,44⟩
  | 3159 => some ⟨3,5,1,0,44⟩
  | 3951 => some ⟨3,5,1,0,44⟩
  | _ => none

def keep_11_20 : List (ℕ × ℤ) := [(79,1),(439,9),(439,4420),(491,5),(491,5076),(2455,1),(2455,26676)]

end Signed39.Contraction
