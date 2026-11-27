import Quantum.Hadamard.ProjectiveFieldModels
import PaleyBits41

open Hadamard.ProjectiveSigning Hadamard.BitTrace
set_option maxHeartbeats 40000000
set_option maxRecDepth 200000
namespace PaleyField41


instance : Fact (Nat.Prime 41) := ⟨by decide⟩
abbrev Element := ZMod 41
def numbers : Fin 41 ≃ Element := Equiv.refl _
private def encode (u : Element) : ℕ := u.val


private def readChar (u : Element) : ℤ :=
  if encode u=0 then 0 else if (1870503675702:ℕ).testBit (encode u) then 1 else -1

private theorem character : ∀u, readChar u=quadraticChar Element u :=
  character_by_squares readChar (by decide +kernel) (by decide +kernel) (by decide +kernel)

def nonsquare : Element := numbers 3
private theorem negative : quadraticChar Element nonsquare= -1 := by
  rw [←character]; decide +kernel

private theorem entries : ∀i j : Fin 42, tableEntry readChar (chart numbers i) (chart numbers j)=
    sign (PaleyBits41.fullRows i) j.val - (if i=j then 1 else 0 : ℤ) := by decide +kernel

theorem card : Fintype.card Element=41 := (Fintype.card_congr numbers.symm).trans (Fintype.card_fin _)


private theorem boundSplitSquares :
    fourFifths 41 ≤ signedDet ((.split true true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 21 ⊕ Fin 21,
      (.split true true : Pattern).read readChar nonsquare (chart numbers (PaleyBits41.SplitSquares.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits41.fullRows entries
    nonsquare (.split true true) PaleyBits41.SplitSquares.indexing diags]
  exact PaleyBits41.SplitSquares.determinant_bound


private theorem boundSplitNonsquares :
    fourFifths 41 ≤ signedDet ((.split false true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 21 ⊕ Fin 21,
      (.split false true : Pattern).read readChar nonsquare (chart numbers (PaleyBits41.SplitNonsquares.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits41.fullRows entries
    nonsquare (.split false true) PaleyBits41.SplitNonsquares.indexing diags]
  exact PaleyBits41.SplitNonsquares.determinant_bound


private theorem boundSplitSquaresOpposite :
    fourFifths 41 ≤ signedDet ((.split false false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 21 ⊕ Fin 21,
      (.split false false : Pattern).read readChar nonsquare (chart numbers (PaleyBits41.SplitSquaresOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits41.fullRows entries
    nonsquare (.split false false) PaleyBits41.SplitSquaresOpposite.indexing diags]
  exact PaleyBits41.SplitSquaresOpposite.determinant_bound


private theorem boundSplitNonsquaresOpposite :
    fourFifths 41 ≤ signedDet ((.split true false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 21 ⊕ Fin 21,
      (.split true false : Pattern).read readChar nonsquare (chart numbers (PaleyBits41.SplitNonsquaresOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits41.fullRows entries
    nonsquare (.split true false) PaleyBits41.SplitNonsquaresOpposite.indexing diags]
  exact PaleyBits41.SplitNonsquaresOpposite.determinant_bound


private theorem boundNonsplitNegative :
    fourFifths 41 ≤ signedDet ((.nonsplit false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 21 ⊕ Fin 21,
      (.nonsplit false : Pattern).read readChar nonsquare (chart numbers (PaleyBits41.NonsplitNegative.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits41.fullRows entries
    nonsquare (.nonsplit false) PaleyBits41.NonsplitNegative.indexing diags]
  exact PaleyBits41.NonsplitNegative.determinant_bound


private theorem boundNonsplitNegativeOpposite :
    fourFifths 41 ≤ signedDet ((.nonsplit true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 21 ⊕ Fin 21,
      (.nonsplit true : Pattern).read readChar nonsquare (chart numbers (PaleyBits41.NonsplitNegativeOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits41.fullRows entries
    nonsquare (.nonsplit true) PaleyBits41.NonsplitNegativeOpposite.indexing diags]
  exact PaleyBits41.NonsplitNegativeOpposite.determinant_bound


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
end PaleyField41
