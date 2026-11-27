import Quantum.Hadamard.ProjectiveFieldModels
import PaleyBits73

open Hadamard.ProjectiveSigning Hadamard.BitTrace
set_option maxHeartbeats 40000000
set_option maxRecDepth 200000
namespace PaleyField73


instance : Fact (Nat.Prime 73) := ⟨by decide⟩
abbrev Element := ZMod 73
def numbers : Fin 73 ≃ Element := Equiv.refl _
private def encode (u : Element) : ℕ := u.val


private def readChar (u : Element) : ℤ :=
  if encode u=0 then 0 else if (9059857384996697084766:ℕ).testBit (encode u) then 1 else -1

private theorem character : ∀u, readChar u=quadraticChar Element u :=
  character_by_squares readChar (by decide +kernel) (by decide +kernel) (by decide +kernel)

def nonsquare : Element := numbers 5
private theorem negative : quadraticChar Element nonsquare= -1 := by
  rw [←character]; decide +kernel

private theorem entries : ∀i j : Fin 74, tableEntry readChar (chart numbers i) (chart numbers j)=
    sign (PaleyBits73.fullRows i) j.val - (if i=j then 1 else 0 : ℤ) := by decide +kernel

theorem card : Fintype.card Element=73 := (Fintype.card_congr numbers.symm).trans (Fintype.card_fin _)


private theorem boundSplitSquares :
    fourFifths 73 ≤ signedDet ((.split true true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 37 ⊕ Fin 37,
      (.split true true : Pattern).read readChar nonsquare (chart numbers (PaleyBits73.SplitSquares.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits73.fullRows entries
    nonsquare (.split true true) PaleyBits73.SplitSquares.indexing diags]
  exact PaleyBits73.SplitSquares.determinant_bound


private theorem boundSplitNonsquares :
    fourFifths 73 ≤ signedDet ((.split false true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 37 ⊕ Fin 37,
      (.split false true : Pattern).read readChar nonsquare (chart numbers (PaleyBits73.SplitNonsquares.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits73.fullRows entries
    nonsquare (.split false true) PaleyBits73.SplitNonsquares.indexing diags]
  exact PaleyBits73.SplitNonsquares.determinant_bound


private theorem boundSplitSquaresOpposite :
    fourFifths 73 ≤ signedDet ((.split false false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 37 ⊕ Fin 37,
      (.split false false : Pattern).read readChar nonsquare (chart numbers (PaleyBits73.SplitSquaresOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits73.fullRows entries
    nonsquare (.split false false) PaleyBits73.SplitSquaresOpposite.indexing diags]
  exact PaleyBits73.SplitSquaresOpposite.determinant_bound


private theorem boundSplitNonsquaresOpposite :
    fourFifths 73 ≤ signedDet ((.split true false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 37 ⊕ Fin 37,
      (.split true false : Pattern).read readChar nonsquare (chart numbers (PaleyBits73.SplitNonsquaresOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits73.fullRows entries
    nonsquare (.split true false) PaleyBits73.SplitNonsquaresOpposite.indexing diags]
  exact PaleyBits73.SplitNonsquaresOpposite.determinant_bound


private theorem boundNonsplitNegative :
    fourFifths 73 ≤ signedDet ((.nonsplit false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 37 ⊕ Fin 37,
      (.nonsplit false : Pattern).read readChar nonsquare (chart numbers (PaleyBits73.NonsplitNegative.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits73.fullRows entries
    nonsquare (.nonsplit false) PaleyBits73.NonsplitNegative.indexing diags]
  exact PaleyBits73.NonsplitNegative.determinant_bound


private theorem boundNonsplitNegativeOpposite :
    fourFifths 73 ≤ signedDet ((.nonsplit true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 37 ⊕ Fin 37,
      (.nonsplit true : Pattern).read readChar nonsquare (chart numbers (PaleyBits73.NonsplitNegativeOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits73.fullRows entries
    nonsquare (.nonsplit true) PaleyBits73.NonsplitNegativeOpposite.indexing diags]
  exact PaleyBits73.NonsplitNegativeOpposite.determinant_bound


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
end PaleyField73
