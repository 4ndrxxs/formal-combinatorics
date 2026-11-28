import MSXProblem15
import Mathlib.FieldTheory.Finite.GaloisField

/-! The row (4) Gauss product of Momihara, Suda and Xiang over an arbitrary
quadratic field extension, with the additive character lifted by the field trace. -/

noncomputable section
open Finset Hadamard.LinPhoa Hadamard.NonsplitTorus Hadamard.NonsplitTorus.MSXTable
open scoped ComplexOrder

namespace Hadamard.MSXProblem15

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {K : Type*} [Field K] [Fintype K] [Algebra F K]
variable {d : F} [Fact (¬ IsSquare d)]

private noncomputable local instance (d : F) : Fintype (Ext d) :=
  Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd d 0).symm

/-- The published row (4) in the field `K`, with its given algebra structure over `F`. -/
def classFourOver (ω : Kˣ) (τ ν : MulChar K ℂ) (ψ : AddChar F ℂ) : ℂ :=
  let q := Fintype.card F
  let Ψ := ψ.compAddMonoidHom (Algebra.trace F K).toAddMonoidHom
  ∏ j ∈ range ((q-1)/2+1), ((q:ℂ)+1 -
    gaussSum (eta F) ψ / (q:ℂ) *
      ∑ ℓ ∈ ({1,3} : Finset ℕ), gaussSum (τ^ℓ * ν^j) Ψ *
        (τ^ℓ)⁻¹ ((ω : K)^((q+1)/2)))

private def pullOne {A B : Type*} [Field A] [Field B] (e : A ≃+* B)
    (χ : MulChar B ℂ) : MulChar A ℂ where
  toFun x := χ (e x)
  map_one' := by simp
  map_mul' x y := by simp
  map_nonunit' x hx := by
    have h : x = 0 := by simpa [isUnit_iff_ne_zero] using hx
    simp [h, MulChar.map_zero]

/-- Pullback along a field isomorphism is an equivalence of multiplicative
character groups, including their zero extensions at the origin. -/
def pullTableCharacter {A B : Type*} [Field A] [Field B] (e : A ≃+* B) :
    MulChar B ℂ ≃* MulChar A ℂ where
  toFun := pullOne e
  invFun := pullOne e.symm
  left_inv χ := by
    apply MulChar.ext'
    intro x
    change χ (e (e.symm x)) = χ x
    rw [e.apply_symm_apply]
  right_inv χ := by
    apply MulChar.ext'
    intro x
    change χ (e.symm (e x)) = χ x
    rw [e.symm_apply_apply]
  map_mul' χ ξ := by
    apply MulChar.ext'
    intro x
    rfl

@[simp] theorem pullTableCharacter_apply {A B : Type*} [Field A] [Field B] (e : A ≃+* B)
    (χ : MulChar B ℂ) (x : A) : pullTableCharacter e χ x = χ (e x) := rfl

omit [DecidableEq F] in
private theorem gauss_pull (e : Ext d ≃ₐ[F] K) (χ : MulChar K ℂ) (ψ : AddChar F ℂ) :
    gaussSum (pullTableCharacter e.toRingEquiv χ) (traceCharacter (d:=d) ψ) =
      gaussSum χ (ψ.compAddMonoidHom (Algebra.trace F K).toAddMonoidHom) := by
  rw [traceCharacter_eq_relativeTrace]
  unfold gaussSum
  calc
    _ = ∑ x : Ext d, χ (e x) * ψ (Algebra.trace F K (e x)) := by
      apply sum_congr rfl
      intro x _
      change χ (e x) * ψ (Algebra.trace F (Ext d) x) = χ (e x) * ψ (Algebra.trace F K (e x))
      rw [Algebra.trace_eq_of_algEquiv]
    _ = _ := e.toEquiv.sum_comp (fun x : K ↦ χ x * ψ (Algebra.trace F K x))

/-- Transport preserves the full row (4), including each Gauss sum and
the inverse quartic phase for the chosen generator. -/
theorem classFour_eq_over_algEquiv (e : Ext d ≃ₐ[F] K) (ω : Kˣ) (τ ν : MulChar K ℂ)
    (ψ : AddChar F ℂ) :
    classFour (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv ω)
      (pullTableCharacter e.toRingEquiv τ) (pullTableCharacter e.toRingEquiv ν) ψ =
        classFourOver ω τ ν ψ := by
  classical
  let E := pullTableCharacter e.toRingEquiv
  let u := Units.mapEquiv e.symm.toRingEquiv.toMulEquiv ω
  have generator : e (u : Ext d) = (ω : K) := e.apply_symm_apply _
  have term (j ℓ : ℕ) :
      gaussSum ((E τ)^ℓ * (E ν)^j) (traceCharacter (d:=d) ψ) *
        ((E τ)^ℓ)⁻¹ ((u : Ext d)^((Fintype.card F+1)/2)) =
      gaussSum (τ^ℓ * ν^j) (ψ.compAddMonoidHom (Algebra.trace F K).toAddMonoidHom) *
        (τ^ℓ)⁻¹ ((ω : K)^((Fintype.card F+1)/2)) := by
    have g : (E τ)^ℓ * (E ν)^j = E (τ^ℓ * ν^j) := by rw [map_mul, map_pow, map_pow]
    have p : ((E τ)^ℓ)⁻¹ = E ((τ^ℓ)⁻¹) := by rw [map_inv, map_pow]
    rw [g, p, gauss_pull, pullTableCharacter_apply]
    change _ * (τ^ℓ)⁻¹ (e ((u : Ext d)^((Fintype.card F+1)/2))) = _
    rw [map_pow, generator]
  unfold classFour classFourOver
  dsimp only
  apply prod_congr rfl
  intro j _
  simp only [← term j, E, u]

open Polynomial in
/-- All quadratic finite-field extensions of the same base split
`X^(q²)-X`, giving an isomorphism fixing the base field. -/
def quadraticModelEquiv (d : F) [Fact (¬ IsSquare d)] (degree : Module.finrank F K = 2) :
    Ext d ≃ₐ[F] K := by
  classical
  have size : Fintype.card (Ext d) = Fintype.card K := by
    rw [Module.card_eq_pow_finrank (K:=F) (V:=K), degree]
    simpa only [Fintype.card_prod, pow_two] using
      Fintype.card_congr (QuadraticAlgebra.equivProd d 0)
  let P : Polynomial F := X ^ Fintype.card K - X
  haveI modelSplits : IsSplittingField F (Ext d) P := by
    dsimp [P]
    rw [← size]
    exact FiniteField.isSplittingField_sub (Ext d) F
  haveI targetSplits : IsSplittingField F K P := FiniteField.isSplittingField_sub K F
  exact (IsSplittingField.algEquiv (Ext d) P).trans (IsSplittingField.algEquiv K P).symm

/-- For the distinguished complex additive character, the Gauss sums on
`F` and on `K` use the respective absolute traces to the prime field. -/
theorem classFourOver_absoluteTraceCharacter (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]
    [Algebra (ZMod p) K] [IsScalarTower (ZMod p) F K] (ω : Kˣ) (τ ν : MulChar K ℂ) :
    classFourOver ω τ ν (absoluteTraceCharacter p F) =
      let q := Fintype.card F
      ∏ j ∈ range ((q-1)/2+1), ((q:ℂ)+1 -
        gaussSum (eta F) (absoluteTraceCharacter p F) / (q:ℂ) *
          ∑ ℓ ∈ ({1,3} : Finset ℕ), gaussSum (τ^ℓ * ν^j) (absoluteTraceCharacter p K) *
            (τ^ℓ)⁻¹ ((ω : K)^((q+1)/2))) := by
  have tower : (absoluteTraceCharacter p F).compAddMonoidHom (Algebra.trace F K).toAddMonoidHom =
      absoluteTraceCharacter p K := by
    ext z
    change ZMod.stdAddChar (Algebra.trace (ZMod p) F (Algebra.trace F K z)) =
      ZMod.stdAddChar (Algebra.trace (ZMod p) K z)
    rw [Algebra.trace_trace]
  unfold classFourOver
  dsimp only
  rw [tower]

/-- The row (4) bound holds in every quadratic finite-field extension, for
every generator and every character of the indicated order. -/
theorem row_four_over (q4 : Fintype.card F % 4 = 1) (lo : 29 ≤ Fintype.card F)
    (degree : Module.finrank F K = 2) (ω : Kˣ) (hω : orderOf ω = Nat.card Kˣ)
    (τ ν : MulChar K ℂ) (hτ : orderOf τ = 4) (hν : orderOf ν = (Fintype.card F+1)/2)
    (ψ : AddChar F ℂ) (prim : ψ.IsPrimitive) :
    (threshold (Fintype.card F) : ℂ) ≤ classFourOver ω τ ν ψ := by
  have hc : ringChar F ≠ 2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  obtain ⟨d, nd⟩ := FiniteField.exists_nonsquare hc
  let : Fact (¬ IsSquare d) := ⟨nd⟩
  let e := quadraticModelEquiv d degree
  let U := Units.mapEquiv e.symm.toRingEquiv.toMulEquiv
  have full : orderOf (U ω) = Nat.card (Ext d)ˣ := by
    rw [U.orderOf_eq, hω]
    exact Nat.card_congr U.toEquiv
  rw [← classFour_eq_over_algEquiv e]
  exact row_four q4 lo (U ω) full _ _ ((pullTableCharacter e.toRingEquiv).orderOf_eq τ |>.trans hτ)
    ((pullTableCharacter e.toRingEquiv).orderOf_eq ν |>.trans hν) ψ prim

/-- Problem 15 in any quadratic finite field, simultaneously for all
parameter choices in the three rows of Theorem 1.6. -/
theorem problem15_over (q4 : Fintype.card F % 4 = 1) (lo : 29 ≤ Fintype.card F)
    (degree : Module.finrank F K = 2) (ω : Kˣ) (hω : orderOf ω = Nat.card Kˣ)
    (τ ν : MulChar K ℂ) (hτ : orderOf τ = 4) (hν : orderOf ν = (Fintype.card F+1)/2)
    (χ : MulChar F ℂ) (hχ : orderOf χ = Fintype.card F-1)
    (ψ : AddChar F ℂ) (prim : ψ.IsPrimitive) :
    let B : ℂ := ((4/5 : ℝ) * ehlichWojtas (Fintype.card F+1) : ℝ)
    B ≤ classFourOver ω τ ν ψ ∧ B ≤ classFive χ ∧ B ≤ classSix χ := by
  dsimp only
  rw [← threshold_at_order q4]
  refine ⟨row_four_over q4 lo degree ω hω τ ν hτ hν ψ prim, ?_⟩
  simpa only [classFive, classSix, threshold, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, Complex.ofReal_one] using msx_table_rows_five_six q4 lo χ hχ

/-- The class (4) generator and both required characters exist in every
quadratic finite-field extension of an eligible base. -/
theorem exists_row_four_parameters_over (q4 : Fintype.card F % 4 = 1)
    (degree : Module.finrank F K = 2) :
    ∃ (ω : Kˣ) (τ ν : MulChar K ℂ),
      orderOf ω = Nat.card Kˣ ∧ orderOf τ = 4 ∧ orderOf ν = (Fintype.card F+1)/2 := by
  have hc : ringChar F ≠ 2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  obtain ⟨d, nd⟩ := FiniteField.exists_nonsquare hc
  let : Fact (¬ IsSquare d) := ⟨nd⟩
  let e := quadraticModelEquiv d degree
  let U := Units.mapEquiv e.toRingEquiv.toMulEquiv
  let C := pullTableCharacter e.symm.toRingEquiv
  obtain ⟨ω, τ, ν, hω, hτ, hν⟩ := exists_parameters (d:=d) q4
  exact ⟨U ω, C τ, C ν, (U.orderOf_eq ω).trans (hω.trans (Nat.card_congr U.toEquiv)),
    (C.orderOf_eq τ).trans hτ, (C.orderOf_eq ν).trans hν⟩

#print axioms classFourOver_absoluteTraceCharacter
#print axioms problem15_over
#print axioms exists_row_four_parameters_over
#print axioms classFour_eq_over_algEquiv
#print axioms quadraticModelEquiv
#print axioms row_four_over

end Hadamard.MSXProblem15
