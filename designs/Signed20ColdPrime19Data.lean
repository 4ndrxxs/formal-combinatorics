import SignedDivisorSlice
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def qInputs_19_20 : ℕ → Option QuotientInput
  | 23 => some ⟨23,5,11,0,76⟩
  | 35 => some ⟨5,19,1,0,20⟩
  | 37 => some ⟨37,5,18,0,76⟩
  | 43 => some ⟨43,5,21,0,76⟩
  | 47 => some ⟨47,5,23,0,76⟩
  | 49 => some ⟨7,5,3,0,76⟩
  | 53 => some ⟨53,5,26,0,76⟩
  | 61 => some ⟨61,5,15,0,76⟩
  | 65 => some ⟨5,19,1,0,20⟩
  | 83 => some ⟨83,5,41,0,76⟩
  | 91 => some ⟨13,5,2,0,76⟩
  | 97 => some ⟨97,19,16,0,20⟩
  | 115 => some ⟨5,19,1,0,20⟩
  | 173 => some ⟨173,5,86,0,76⟩
  | 185 => some ⟨5,19,1,0,20⟩
  | 217 => some ⟨7,5,3,0,76⟩
  | 235 => some ⟨5,19,1,0,20⟩
  | 299 => some ⟨13,5,2,0,76⟩
  | 455 => some ⟨5,19,1,0,20⟩
  | 463 => some ⟨463,5,231,0,76⟩
  | 679 => some ⟨7,5,3,0,76⟩
  | 767 => some ⟨13,5,2,0,76⟩
  | 851 => some ⟨23,5,11,0,76⟩
  | 977 => some ⟨977,5,488,0,76⟩
  | 1211 => some ⟨7,5,3,0,76⟩
  | 1519 => some ⟨7,5,3,0,76⟩
  | 1895 => some ⟨5,19,1,0,20⟩
  | 2279 => some ⟨43,5,21,0,76⟩
  | 4255 => some ⟨5,19,1,0,20⟩
  | 6839 => some ⟨7,5,3,0,76⟩
  | _ => none

def keep_19_20 : List (ℕ × ℤ) := [(31,49),(59,104),(59,541),(71,4),(79,329),(79,424),(151,1),(379,20),(379,6461),(911,1),(3191,1),(3191,60136),(5471,1),(5471,103304)]

end Signed39.Contraction
