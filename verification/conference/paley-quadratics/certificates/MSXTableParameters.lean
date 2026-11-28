import PaleyNonsplitTorus
import MSXTableCyclic
import Mathlib.FieldTheory.Cardinality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.LegendreSymbol.Complex

/-! Existence of the finite fields and character parameters used in rows
(4), (5), and (6) of Theorem 1.6 in Momihara, Suda and Xiang. -/

noncomputable section
open Hadamard.NonsplitTorus

namespace Hadamard.MSXProblem15

private noncomputable local instance {F : Type} [Field F] [Fintype F] (d : F) :
    Fintype (Ext d) := Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd d 0).symm

/-- All generator and character choices in the printed products exist
over each eligible field. The additive character on the extension is
obtained from the base character by composition with the trace. -/
theorem exists_table_parameters (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (q4 : Fintype.card F % 4 = 1) (lo : 29 ≤ Fintype.card F) :
    (∃ χ : MulChar F ℂ, orderOf χ = Fintype.card F - 1) ∧
    (∃ ψ : AddChar F ℂ, ψ.IsPrimitive) ∧
    ∃ d : F, ∃ ns : ¬ IsSquare d, letI : Fact (¬ IsSquare d) := ⟨ns⟩
      (∃ ω : (Ext d)ˣ, orderOf ω = Nat.card (Ext d)ˣ) ∧
      (∃ τ : MulChar (Ext d) ℂ, orderOf τ = 4) ∧
      (∃ ν : MulChar (Ext d) ℂ, orderOf ν = (Fintype.card F + 1) / 2) := by
  classical
  let q := Fintype.card F
  have hc : ringChar F ≠ 2 := by
    intro h
    have even := FiniteField.even_card_of_char_two h
    omega
  obtain ⟨d,ns⟩ := FiniteField.exists_nonsquare hc
  let : Fact (¬ IsSquare d) := ⟨ns⟩
  have basepos : 0 < q-1 := by dsimp [q]; omega
  let : NeZero (q-1) := ⟨basepos.ne'⟩
  obtain ⟨z,zord⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ (q-1)
  obtain ⟨ω,τ,ν,hω,hτ,hν⟩ := MSXTable.exists_parameters (d:=d) q4
  exact ⟨MulChar.exists_mulChar_orderOf F (dvd_refl _) zord,
    ⟨AddChar.FiniteField.primitiveChar_to_Complex F, AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F⟩,
    d,ns,⟨ω,hω⟩,⟨τ,hτ⟩,⟨ν,hν⟩⟩

/-- Every prime power in the numerical question has a field model on its
own finite index type. -/
theorem field_at_every_prime_power (q : ℕ) (h : IsPrimePow q) : Nonempty (Field (Fin q)) :=
  Fintype.nonempty_field_iff.mpr (by simpa using h)

#print axioms exists_table_parameters
#print axioms field_at_every_prime_power

end Hadamard.MSXProblem15
