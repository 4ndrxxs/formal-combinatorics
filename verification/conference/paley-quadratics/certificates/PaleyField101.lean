import Quantum.Hadamard.ProjectiveFieldModels
import PaleyBits101

open Hadamard.ProjectiveSigning Hadamard.BitTrace
set_option maxHeartbeats 40000000
set_option maxRecDepth 200000
namespace PaleyField101


instance : Fact (Nat.Prime 101) := ⟨by decide⟩
abbrev Element := ZMod 101
def numbers : Fin 101 ≃ Element := Equiv.refl _
private def encode (u : Element) : ℕ := u.val


private def readChar (u : Element) : ℤ :=
  if encode u=0 then 0 else if (1550432784880709368503235994226:ℕ).testBit (encode u) then 1 else -1

private theorem character : ∀u, readChar u=quadraticChar Element u :=
  character_by_squares readChar (by decide +kernel) (by decide +kernel) (by decide +kernel)

def nonsquare : Element := numbers 2
private theorem negative : quadraticChar Element nonsquare= -1 := by
  rw [←character]; decide +kernel

private theorem entries : ∀i j : Fin 102, tableEntry readChar (chart numbers i) (chart numbers j)=
    sign (PaleyBits101.fullRows i) j.val - (if i=j then 1 else 0 : ℤ) := by decide +kernel

theorem card : Fintype.card Element=101 := (Fintype.card_congr numbers.symm).trans (Fintype.card_fin _)


private theorem boundSplitSquares :
    fourFifths 101 ≤ signedDet ((.split true true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 51 ⊕ Fin 51,
      (.split true true : Pattern).read readChar nonsquare (chart numbers (PaleyBits101.SplitSquares.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits101.fullRows entries
    nonsquare (.split true true) PaleyBits101.SplitSquares.indexing diags]
  exact PaleyBits101.SplitSquares.determinant_bound


private theorem boundSplitNonsquares :
    fourFifths 101 ≤ signedDet ((.split false true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 51 ⊕ Fin 51,
      (.split false true : Pattern).read readChar nonsquare (chart numbers (PaleyBits101.SplitNonsquares.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits101.fullRows entries
    nonsquare (.split false true) PaleyBits101.SplitNonsquares.indexing diags]
  exact PaleyBits101.SplitNonsquares.determinant_bound


private theorem boundSplitSquaresOpposite :
    fourFifths 101 ≤ signedDet ((.split false false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 51 ⊕ Fin 51,
      (.split false false : Pattern).read readChar nonsquare (chart numbers (PaleyBits101.SplitSquaresOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits101.fullRows entries
    nonsquare (.split false false) PaleyBits101.SplitSquaresOpposite.indexing diags]
  exact PaleyBits101.SplitSquaresOpposite.determinant_bound


private theorem boundSplitNonsquaresOpposite :
    fourFifths 101 ≤ signedDet ((.split true false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 51 ⊕ Fin 51,
      (.split true false : Pattern).read readChar nonsquare (chart numbers (PaleyBits101.SplitNonsquaresOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits101.fullRows entries
    nonsquare (.split true false) PaleyBits101.SplitNonsquaresOpposite.indexing diags]
  exact PaleyBits101.SplitNonsquaresOpposite.determinant_bound


private theorem boundNonsplitNegative :
    fourFifths 101 ≤ signedDet ((.nonsplit false : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 51 ⊕ Fin 51,
      (.nonsplit false : Pattern).read readChar nonsquare (chart numbers (PaleyBits101.NonsplitNegative.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits101.fullRows entries
    nonsquare (.nonsplit false) PaleyBits101.NonsplitNegative.indexing diags]
  exact PaleyBits101.NonsplitNegative.determinant_bound


private theorem boundNonsplitNegativeOpposite :
    fourFifths 101 ≤ signedDet ((.nonsplit true : Pattern).sign nonsquare) := by
  have diags : ∀i : Fin 51 ⊕ Fin 51,
      (.nonsplit true : Pattern).read readChar nonsquare (chart numbers (PaleyBits101.NonsplitNegativeOpposite.indexing i))
      =Sum.elim (fun _ ↦ (1:ℤ)) (fun _ ↦ -1) i := by decide +kernel
  rw [determinant_from_table numbers readChar character PaleyBits101.fullRows entries
    nonsquare (.nonsplit true) PaleyBits101.NonsplitNegativeOpposite.indexing diags]
  exact PaleyBits101.NonsplitNegativeOpposite.determinant_bound


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
end PaleyField101
