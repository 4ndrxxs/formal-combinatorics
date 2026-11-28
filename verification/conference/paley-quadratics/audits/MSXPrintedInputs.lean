import MSXProblem15Statement

/-! Independent check that every admissible integer q supplies all the field,
tower, generator and character hypotheses of printed_determinants at once. -/

noncomputable section
open Hadamard.NonsplitTorus Hadamard.MSXProblem15

namespace MSXVerification

structure PrintedInputs (q : ℕ) where
  p : ℕ
  [prime : Fact p.Prime]
  F : Type
  [baseField : Field F]
  [baseFinite : Fintype F]
  [baseEquality : DecidableEq F]
  K : Type
  [extensionField : Field K]
  [extensionFinite : Fintype K]
  [relativeAlgebra : Algebra F K]
  [primeBase : Algebra (ZMod p) F]
  [primeExtension : Algebra (ZMod p) K]
  [tower : IsScalarTower (ZMod p) F K]
  baseOrder : Fintype.card F = q
  rankTwo : Module.finrank F K = 2
  generator : Kˣ
  quartic : MulChar K ℂ
  torus : MulChar K ℂ
  primitive : MulChar F ℂ
  generatorOrder : orderOf generator = Nat.card Kˣ
  quarticOrder : orderOf quartic = 4
  torusOrder : orderOf torus = (q+1)/2
  primitiveOrder : orderOf primitive = q-1

theorem printed_inputs_exist (q : ℕ) (pp : IsPrimePow q) (q4 : q%4=1) (lo : 29≤q) :
    Nonempty (PrintedInputs q) := by
  classical
  obtain ⟨p,e,hp,he,peq⟩ := pp
  let : Fact p.Prime := ⟨hp.nat_prime⟩
  let F := GaloisField p e
  let : Fintype F := Fintype.ofFinite F
  have card : Fintype.card F = q :=
    Fintype.card_eq_nat_card.trans ((GaloisField.card p e he.ne').trans peq)
  obtain ⟨⟨χ,hχ⟩,_,d,ns,choices⟩ := exists_table_parameters F
    (by simpa only [card] using q4) (by simpa only [card] using lo)
  let : Fact (¬ IsSquare d) := ⟨ns⟩
  let : Fintype (Ext d) :=
    Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd d 0).symm
  obtain ⟨⟨ω,hω⟩,⟨τ,hτ⟩,ν,hν⟩ := choices
  exact ⟨{
    p := p
    F := F
    K := Ext d
    baseOrder := card
    rankTwo := QuadraticAlgebra.finrank_eq_two d 0
    generator := ω
    quartic := τ
    torus := ν
    primitive := χ
    generatorOrder := hω
    quarticOrder := hτ
    torusOrder := by simpa only [card] using hν
    primitiveOrder := by simpa only [card] using hχ
  }⟩

#print axioms printed_inputs_exist
end MSXVerification
