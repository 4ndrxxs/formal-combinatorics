import Quantum.Hadamard.ProjectiveFieldModels
import PaleyBits37

open Hadamard.ProjectiveSigning Hadamard.BitTrace
set_option maxHeartbeats 40000000
set_option maxRecDepth 200000
namespace PaleyField37


instance : Fact (Nat.Prime 37) := ⟨by decide⟩
abbrev Element := ZMod 37
def numbers : Fin 37 ≃ Element := Equiv.refl _
private def encode (u : Element) : ℕ := u.val


private def readChar (u : Element) : ℤ :=
  if encode u=0 then 0 else if (96068509338:ℕ).testBit (encode u) then 1 else -1

private theorem character : ∀u, readChar u=quadraticChar Element u :=
  character_by_squares readChar (by decide +kernel) (by decide +kernel) (by decide +kernel)

def nonsquare : Element := numbers 2
private theorem negative : quadraticChar Element nonsquare= -1 := by
  rw [←character]; decide +kernel

private theorem entries : ∀i j : Fin 38, tableEntry readChar (chart numbers i) (chart numbers j)=
    sign (PaleyBits37.fullRows i) j.val - (if i=j then 1 else 0 : ℤ) := by decide +kernel

theorem card : Fintype.card Element=37 := (Fintype.card_congr numbers.symm).trans (Fintype.card_fin _)


private theorem boundSplitSquares :
    fourFifths 37 ≤ signedDet ((.split true true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 19 ⊕ Fin 19,
      (.split true true : Pattern).read readChar nonsquare (chart numbers (PaleyBits37.SplitSquares.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits37.fullRows entries
    nonsquare (.split true true) PaleyBits37.SplitSquares.indexing diags]
  exact PaleyBits37.SplitSquares.determinant_bound


private theorem boundSplitNonsquares :
    fourFifths 37 ≤ signedDet ((.split false true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 19 ⊕ Fin 19,
      (.split false true : Pattern).read readChar nonsquare (chart numbers (PaleyBits37.SplitNonsquares.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits37.fullRows entries
    nonsquare (.split false true) PaleyBits37.SplitNonsquares.indexing diags]
  exact PaleyBits37.SplitNonsquares.determinant_bound


private theorem boundSplitSquaresOpposite :
    fourFifths 37 ≤ signedDet ((.split false false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 19 ⊕ Fin 19,
      (.split false false : Pattern).read readChar nonsquare (chart numbers (PaleyBits37.SplitSquaresOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits37.fullRows entries
    nonsquare (.split false false) PaleyBits37.SplitSquaresOpposite.indexing diags]
  exact PaleyBits37.SplitSquaresOpposite.determinant_bound


private theorem boundSplitNonsquaresOpposite :
    fourFifths 37 ≤ signedDet ((.split true false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 19 ⊕ Fin 19,
      (.split true false : Pattern).read readChar nonsquare (chart numbers (PaleyBits37.SplitNonsquaresOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits37.fullRows entries
    nonsquare (.split true false) PaleyBits37.SplitNonsquaresOpposite.indexing diags]
  exact PaleyBits37.SplitNonsquaresOpposite.determinant_bound


private theorem boundNonsplitNegative :
    fourFifths 37 ≤ signedDet ((.nonsplit false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 19 ⊕ Fin 19,
      (.nonsplit false : Pattern).read readChar nonsquare (chart numbers (PaleyBits37.NonsplitNegative.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits37.fullRows entries
    nonsquare (.nonsplit false) PaleyBits37.NonsplitNegative.indexing diags]
  exact PaleyBits37.NonsplitNegative.determinant_bound


private theorem boundNonsplitNegativeOpposite :
    fourFifths 37 ≤ signedDet ((.nonsplit true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 19 ⊕ Fin 19,
      (.nonsplit true : Pattern).read readChar nonsquare (chart numbers (PaleyBits37.NonsplitNegativeOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits37.fullRows entries
    nonsquare (.nonsplit true) PaleyBits37.NonsplitNegativeOpposite.indexing diags]
  exact PaleyBits37.NonsplitNegativeOpposite.determinant_bound


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
end PaleyField37
