import Quantum.Hadamard.ProjectiveFieldModels
import PaleyBits97

open Hadamard.ProjectiveSigning Hadamard.BitTrace
set_option maxHeartbeats 40000000
set_option maxRecDepth 200000
namespace PaleyField97


instance : Fact (Nat.Prime 97) := ⟨by decide⟩
abbrev Element := ZMod 97
def numbers : Fin 97 ≃ Element := Equiv.refl _
private def encode (u : Element) : ℕ := u.val


private def readChar (u : Element) : ℤ :=
  if encode u=0 then 0 else if (152076272278209298711361952606:ℕ).testBit (encode u) then 1 else -1

private theorem character : ∀u, readChar u=quadraticChar Element u :=
  character_by_squares readChar (by decide +kernel) (by decide +kernel) (by decide +kernel)

def nonsquare : Element := numbers 5
private theorem negative : quadraticChar Element nonsquare= -1 := by
  rw [←character]; decide +kernel

private theorem entries : ∀i j : Fin 98, tableEntry readChar (chart numbers i) (chart numbers j)=
    sign (PaleyBits97.fullRows i) j.val - (if i=j then 1 else 0 : ℤ) := by decide +kernel

theorem card : Fintype.card Element=97 := (Fintype.card_congr numbers.symm).trans (Fintype.card_fin _)


private theorem boundSplitSquares :
    fourFifths 97 ≤ signedDet ((.split true true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 49 ⊕ Fin 49,
      (.split true true : Pattern).read readChar nonsquare (chart numbers (PaleyBits97.SplitSquares.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits97.fullRows entries
    nonsquare (.split true true) PaleyBits97.SplitSquares.indexing diags]
  exact PaleyBits97.SplitSquares.determinant_bound


private theorem boundSplitNonsquares :
    fourFifths 97 ≤ signedDet ((.split false true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 49 ⊕ Fin 49,
      (.split false true : Pattern).read readChar nonsquare (chart numbers (PaleyBits97.SplitNonsquares.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits97.fullRows entries
    nonsquare (.split false true) PaleyBits97.SplitNonsquares.indexing diags]
  exact PaleyBits97.SplitNonsquares.determinant_bound


private theorem boundSplitSquaresOpposite :
    fourFifths 97 ≤ signedDet ((.split false false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 49 ⊕ Fin 49,
      (.split false false : Pattern).read readChar nonsquare (chart numbers (PaleyBits97.SplitSquaresOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits97.fullRows entries
    nonsquare (.split false false) PaleyBits97.SplitSquaresOpposite.indexing diags]
  exact PaleyBits97.SplitSquaresOpposite.determinant_bound


private theorem boundSplitNonsquaresOpposite :
    fourFifths 97 ≤ signedDet ((.split true false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 49 ⊕ Fin 49,
      (.split true false : Pattern).read readChar nonsquare (chart numbers (PaleyBits97.SplitNonsquaresOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits97.fullRows entries
    nonsquare (.split true false) PaleyBits97.SplitNonsquaresOpposite.indexing diags]
  exact PaleyBits97.SplitNonsquaresOpposite.determinant_bound


private theorem boundNonsplitNegative :
    fourFifths 97 ≤ signedDet ((.nonsplit false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 49 ⊕ Fin 49,
      (.nonsplit false : Pattern).read readChar nonsquare (chart numbers (PaleyBits97.NonsplitNegative.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits97.fullRows entries
    nonsquare (.nonsplit false) PaleyBits97.NonsplitNegative.indexing diags]
  exact PaleyBits97.NonsplitNegative.determinant_bound


private theorem boundNonsplitNegativeOpposite :
    fourFifths 97 ≤ signedDet ((.nonsplit true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 49 ⊕ Fin 49,
      (.nonsplit true : Pattern).read readChar nonsquare (chart numbers (PaleyBits97.NonsplitNegativeOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits97.fullRows entries
    nonsquare (.nonsplit true) PaleyBits97.NonsplitNegativeOpposite.indexing diags]
  exact PaleyBits97.NonsplitNegativeOpposite.determinant_bound


theorem canonical : CertifiedPatterns Element := by
  refine ⟨nonsquare,negative,?_⟩
  intro pat
  rw [card]
  cases pat with
  | split o z =>
    cases o <;> cases z
    · exact boundSplitSquaresOpposite
    · exact boundSplitNonsquares
    · exact boundSplitNonsquaresOpposite
    · exact boundSplitSquares
  | nonsplit o =>
    cases o
    · exact boundNonsplitNegative
    · exact boundNonsplitNegativeOpposite

#print axioms canonical
end PaleyField97
