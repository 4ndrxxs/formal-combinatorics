import MSXTableExtension

/-! Source-faithful statement of Problem 15, with the three products of
Momihara, Suda and Xiang, Theorem 1.6, and canonical additive characters.
The final corollary makes explicit the published identities attaching
these numbers to the three matrix families. -/

noncomputable section
open Finset Hadamard.MSXProblem15 Hadamard.NonsplitTorus.MSXTable
open scoped ComplexOrder

namespace Hadamard.MSXProblem15

variable {F K : Type} [Field F] [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [Algebra F K]

/-- The numerical statement using the prime-field trace on each field.
Every right side appears explicitly, and the lower bound is expressed at
the original matrix order. -/
theorem printed_determinants (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]
    [Algebra (ZMod p) K] [IsScalarTower (ZMod p) F K]
    (q4 : Fintype.card F % 4 = 1) (lo : 30 ≤ Fintype.card F+1)
    (quadratic : Module.finrank F K=2) (ω : Kˣ) (hω : orderOf ω = Nat.card Kˣ)
    (τ ν : MulChar K ℂ) (hτ : orderOf τ = 4) (hν : orderOf ν = (Fintype.card F+1)/2)
    (χ : MulChar F ℂ) (hχ : orderOf χ = Fintype.card F-1) :
    let q := Fintype.card F
    let n := q+1
    let W : ℝ := (2*(n:ℝ)-2)*((n:ℝ)-2)^((n-2)/2)
    let B : ℂ := ((4/5:ℝ)*W : ℝ)
    let η := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
    let ψF := ZMod.stdAddChar.compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom
    let ψK := ZMod.stdAddChar.compAddMonoidHom (Algebra.trace (ZMod p) K).toAddMonoidHom
    B ≤ ∏ j ∈ range ((q-1)/2+1), ((q:ℂ)+1-gaussSum η ψF/(q:ℂ)*
      ∑ ℓ ∈ ({1,3}:Finset ℕ), gaussSum (τ^ℓ*ν^j) ψK*(τ^ℓ)⁻¹ ((ω:K)^((q+1)/2))) ∧
    B ≤ ((q:ℂ)-1)^2 * ∏ j ∈ Icc 1 ((q-3)/2),
      ((q:ℂ)+1+jacobiSum (η*χ^j) η+jacobiSum (χ^j) η) ∧
    B ≤ ((q:ℂ)^2+2*(q:ℂ)+5) * ∏ j ∈ Icc 1 ((q-3)/2),
      ((q:ℂ)+1-jacobiSum (η*χ^j) η-jacobiSum (χ^j) η) := by
  have h := problem15_over q4 (by omega) quadratic ω hω τ ν hτ hν χ hχ
    (absoluteTraceCharacter p F) (absoluteTraceCharacter_isPrimitive p F)
  rw [classFourOver_absoluteTraceCharacter p] at h
  exact h

/-- Apply the three bounds to integer matrices using the three determinant
identities from the original table. Each such identity is an explicit
hypothesis of this transfer lemma. The preceding theorem proves the three
scalar inequalities independently of those hypotheses. -/
theorem matrix_determinants_of_table
    (q4 : Fintype.card F % 4 = 1) (lo : 30 ≤ Fintype.card F+1)
    (quadratic : Module.finrank F K=2) (ω : Kˣ) (hω : orderOf ω = Nat.card Kˣ)
    (τ ν : MulChar K ℂ) (hτ : orderOf τ = 4) (hν : orderOf ν = (Fintype.card F+1)/2)
    (χ : MulChar F ℂ) (hχ : orderOf χ = Fintype.card F-1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (M₄ M₅ M₆ : Matrix (Fin (Fintype.card F+1)) (Fin (Fintype.card F+1)) ℤ)
    (source₄ : ((|M₄.det|:ℤ):ℂ) = classFourOver ω τ ν ψ)
    (source₅ : ((|M₅.det|:ℤ):ℂ) = classFive χ)
    (source₆ : ((|M₆.det|:ℤ):ℂ) = classSix χ) :
    let B := (4/5:ℝ)*ehlichWojtas (Fintype.card F+1)
    B ≤ (|M₄.det|:ℤ) ∧ B ≤ (|M₅.det|:ℤ) ∧ B ≤ (|M₆.det|:ℤ) := by
  have h := problem15_over q4 (by omega) quadratic ω hω τ ν hτ hν χ hχ ψ hψ
  dsimp only at h ⊢
  rw [←source₄,←source₅,←source₆] at h
  have castInt (x : ℤ) : ((x:ℝ):ℂ) = (x:ℂ) := by norm_cast
  refine ⟨Complex.real_le_real.mp ?_, Complex.real_le_real.mp ?_, Complex.real_le_real.mp ?_⟩
  · simpa only [castInt] using h.1
  · simpa only [castInt] using h.2.1
  · simpa only [castInt] using h.2.2

#print axioms printed_determinants
#print axioms matrix_determinants_of_table

end Hadamard.MSXProblem15
