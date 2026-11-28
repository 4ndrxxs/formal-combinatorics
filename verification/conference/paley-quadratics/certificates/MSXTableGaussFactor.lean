import Quantum.Hadamard.NonsplitCharacterProduct
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RingTheory.QuadraticAlgebra

/-! The two quartic Gauss terms in row (4) of Momihara–Suda–Xiang,
Theorem 1.6. The phase at the trace-zero element determines one orientation
for every Fourier mode of the odd norm-one torus. -/

noncomputable section
open Finset Hadamard.LinPhoa
namespace Hadamard.NonsplitTorus.MSXTable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {d : F} [Fact (¬ IsSquare d)]

private noncomputable local instance (d : F) : Fintype (Ext d) :=
  Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd d 0).symm

omit [Fintype F] [DecidableEq F] [Fact (¬ IsSquare d)] in
/-- The coordinate `2 re(z)` is the field trace from the quadratic algebra. -/
theorem traceCharacter_eq_relativeTrace (ψ : AddChar F ℂ) :
    traceCharacter (d := d) ψ = ψ.compAddMonoidHom (Algebra.trace F (Ext d)).toAddMonoidHom := by
  ext z
  change ψ (2 * z.re) = ψ (Algebra.trace F (Ext d) z)
  rw [Algebra.trace_quadraticAlgebra_apply, QuadraticAlgebra.trace_def, zero_mul, add_zero]

/-- The usual complex additive character obtained by applying `exp(2πi·/p)`
to the absolute trace. -/
def absoluteTraceCharacter (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [Algebra (ZMod p) K] : AddChar K ℂ :=
  ZMod.stdAddChar.compAddMonoidHom (Algebra.trace (ZMod p) K).toAddMonoidHom

theorem absoluteTraceCharacter_apply (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [Algebra (ZMod p) K] (z : K) :
    absoluteTraceCharacter p K z =
      Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace (ZMod p) K z).val / p) :=
  ZMod.toCircle_apply _

theorem absoluteTraceCharacter_isPrimitive (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [Finite K] [Algebra (ZMod p) K] : (absoluteTraceCharacter p K).IsPrimitive := by
  obtain ⟨z, hz⟩ := Algebra.trace_surjective (ZMod p) K 1
  apply AddChar.IsPrimitive.of_ne_one
  refine AddChar.ne_one_iff.mpr ⟨z, ?_⟩
  change ZMod.stdAddChar (Algebra.trace (ZMod p) K z) ≠ 1
  rw [hz, ← (ZMod.stdAddChar (N := p)).map_zero_eq_one]
  exact ZMod.injective_stdAddChar.ne one_ne_zero

omit [DecidableEq F] in
/-- The absolute-trace characters used in the two Gauss sums agree under
relative trace, by trace transitivity in the tower `𝔽ₚ ⊆ F ⊆ Ext d`. -/
theorem traceCharacter_absoluteTraceCharacter (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] :
    traceCharacter (d := d) (absoluteTraceCharacter p F) = absoluteTraceCharacter p (Ext d) := by
  rw [traceCharacter_eq_relativeTrace]
  ext z
  change ZMod.stdAddChar (Algebra.trace (ZMod p) F (Algebra.trace F (Ext d) z)) =
    ZMod.stdAddChar (Algebra.trace (ZMod p) (Ext d) z)
  rw [Algebra.trace_trace]

/-- The correction in the published row, with its two inverse quartic phases. -/
def msxTableCorrection (τ χ : MulChar (Ext d) ℂ) (w : Ext d) (ψ : AddChar F ℂ) : ℂ :=
  gaussSum (eta F) ψ / (Fintype.card F : ℂ) *
    (gaussSum (τ * χ) (traceCharacter ψ) * τ⁻¹ w +
      gaussSum (τ ^ 3 * χ) (traceCharacter ψ) * (τ ^ 3)⁻¹ w)

/-- Expanded with the canonical additive character on each of the two fields. -/
theorem msxTableCorrection_absoluteTraceCharacter (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]
    (τ χ : MulChar (Ext d) ℂ) (w : Ext d) :
    msxTableCorrection τ χ w (absoluteTraceCharacter p F) =
      gaussSum (eta F) (absoluteTraceCharacter p F) / (Fintype.card F : ℂ) *
        (gaussSum (τ * χ) (absoluteTraceCharacter p (Ext d)) * τ⁻¹ w +
          gaussSum (τ ^ 3 * χ) (absoluteTraceCharacter p (Ext d)) * (τ ^ 3)⁻¹ w) := by
  rw [msxTableCorrection, traceCharacter_absoluteTraceCharacter]

#print axioms traceCharacter_absoluteTraceCharacter

/-- Here `k` is the scalar for which `2√d = k w`. -/
def msxTableOrientation (k : Fˣ) : ℤ := -quadraticChar F (k : F)

theorem msxTableOrientation_sq (k : Fˣ) : msxTableOrientation k ^ 2 = 1 := by
  simpa only [msxTableOrientation, neg_sq] using quadraticChar_sq_one k.ne_zero

/-- A quartic character whose square is the extension quadratic character
is trivial on the odd norm-one torus. -/
theorem quartic_on_spin (q4 : Fintype.card F % 4 = 1) (hm : quadraticChar F (-1) = 1)
    (h : (Ext d)ˣ) (ho : orderOf h = (Fintype.card F + 1) / 2) (hn : (h : Ext d).norm = 1)
    (τ : MulChar (Ext d) ℂ) (quartic : τ ^ 2 = eta (Ext d)) (i : Fin (orderOf h)) :
    τ (spin h i) = 1 := by
  have square : τ (h : Ext d) ^ 2 = 1 := by
    rw [← MulChar.pow_apply_coe τ 2 h, quartic, ← normCharacter_eq_quadratic hm]
    change eta F (h : Ext d).norm = 1
    rw [hn, map_one]
  have period : (h : Ext d) ^ orderOf h = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val (pow_orderOf_eq_one h)
  have odd : Odd (orderOf h) := ⟨Fintype.card F / 4, by omega⟩
  have trivial : τ (h : Ext d) = 1 := by
    rcases sq_eq_one_iff.mp square with pos | neg
    · exact pos
    · have eq := congrArg τ period
      rw [map_pow, map_one, neg, odd.neg_one_pow] at eq
      norm_num at eq
  simp [spin, map_pow, trivial]

private theorem base_gauss_sq (hc : ringChar F ≠ 2) (hm : quadraticChar F (-1) = 1)
    (ψ : AddChar F ℂ) (primitive : ψ.IsPrimitive) : gaussSum (eta F) ψ ^ 2 = Fintype.card F := by
  have ne : eta F ≠ 1 := (MulChar.ringHomComp_ne_one_iff
    (by exact_mod_cast (Int.cast_injective (α := ℂ)))).mpr (quadraticChar_ne_one hc)
  have neg : eta F (-1) = 1 := by
    change (quadraticChar F (-1) : ℂ) = 1
    rw [hm, Int.cast_one]
  simpa only [neg, one_mul] using gaussSum_sq ne
    ((quadraticChar_isQuadratic F).comp (Int.castRingHom ℂ)) primitive

/-- The correction equals twice a torus Fourier coefficient with a sign
depending only on the trace-zero point and the quadratic coordinates. -/
theorem msxTableCorrection_eq_torusSymbol
    (hc : ringChar F ≠ 2) (q4 : Fintype.card F % 4 = 1) (hm : quadraticChar F (-1) = 1)
    (h : (Ext d)ˣ) [NeZero (orderOf h)]
    (ho : orderOf h = (Fintype.card F + 1) / 2) (hn : (h : Ext d).norm = 1)
    (τ χ : MulChar (Ext d) ℂ) (quartic : τ ^ 2 = eta (Ext d))
    (τbase : ∀ s : F, τ (algebraMap F (Ext d) s) = eta F s)
    (χbase : ∀ s : Fˣ, χ (algebraMap F (Ext d) (s : F)) = 1)
    (w : Ext d) (χw : χ w = 1) (k : Fˣ)
    (coord : twiceRoot d = algebraMap F (Ext d) (k : F) * w)
    (θ : AddChar (Fin (orderOf h)) ℂ) (spins : ∀ i, χ (spin h i) = θ i)
    (ψ : AddChar F ℂ) (primitive : ψ.IsPrimitive) :
    msxTableCorrection τ χ w ψ = 2 * (msxTableOrientation k : ℂ) * torusSymbol h θ := by
  let Ω := τ * χ
  have base (s : F) : Ω (algebraMap F (Ext d) s) = eta F s := by
    by_cases z : s = 0
    · subst s
      rw [map_zero, show Ω 0 = 0 from Ω.map_nonunit (by simp),
        show eta F 0 = 0 from (eta F).map_nonunit (by simp)]
    · have e := χbase (Units.mk0 s z)
      change χ (algebraMap F (Ext d) s) = 1 at e
      simp only [Ω, MulChar.mul_apply, τbase, e, mul_one]
  have torus (i : Fin (orderOf h)) : Ω (spin h i) = θ i := by
    simp only [Ω, MulChar.mul_apply, quartic_on_spin q4 hm h ho hn τ quartic,
      one_mul, spins]
  have twist : Ω * normCharacter (d := d) = τ ^ 3 * χ := by
    rw [normCharacter_eq_quadratic hm, ← quartic]
    simp only [Ω, pow_succ, pow_zero, one_mul]
    ac_rfl
  have difference := torus_gauss_difference hc q4 hm h ho hn Ω base ψ
  rw [twist] at difference
  simp only [torus] at difference
  have phase : Ω (twiceRoot d) = eta F (k : F) * τ w := by
    rw [coord, map_mul, base]
    simp [Ω, χw]
  have ksq : eta F (k : F) ^ 2 = 1 := by
    change (quadraticChar F (k : F) : ℂ) ^ 2 = 1
    exact_mod_cast quadraticChar_sq_one k.ne_zero
  have usq := torus_gauss_phase hc Ω base
  rw [phase, mul_pow, ksq, one_mul] at usq
  have inversePhase : (τ w)⁻¹ = -τ w := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination -usq
  have first : τ⁻¹ w = -τ w := by rw [MulChar.inv_apply_eq_inv', inversePhase]
  have third : (τ ^ 3)⁻¹ w = τ w := by
    rw [MulChar.inv_apply_eq_inv', MulChar.pow_apply' τ (by decide : 3 ≠ 0),
      show τ w ^ 3 = -τ w by rw [pow_succ, usq, neg_one_mul], inv_neg, inversePhase, neg_neg]
  rw [phase] at difference
  let G := gaussSum (eta F) ψ
  let A := gaussSum (τ * χ) (traceCharacter ψ)
  let B := gaussSum (τ ^ 3 * χ) (traceCharacter ψ)
  change (eta F (k : F) * τ w) * (A - B) = 2 * G * torusSymbol h θ at difference
  have weighted : A * τ⁻¹ w + B * (τ ^ 3)⁻¹ w = -(eta F (k : F)) * (2 * G * torusSymbol h θ) := by
    rw [first, third, ← difference]
    linear_combination (τ w * (A - B)) * ksq
  have gsq : G ^ 2 = (Fintype.card F : ℂ) := base_gauss_sq hc hm ψ primitive
  have qne : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := F)
  change G / (Fintype.card F : ℂ) * (A * τ⁻¹ w + B * (τ ^ 3)⁻¹ w) = _
  rw [weighted]
  calc
    _ = 2 * (-eta F (k : F)) * torusSymbol h θ * (G ^ 2 / (Fintype.card F : ℂ)) := by ring
    _ = _ := by rw [gsq, div_self qne, mul_one]; simp [msxTableOrientation, eta]

#print axioms msxTableCorrection_eq_torusSymbol

omit [Fintype F] [DecidableEq F] [Fact (¬ IsSquare d)] in
private theorem pow_on_trivial_value (χ : MulChar (Ext d) ℂ) (a : Ext d)
    (ha : χ a = 1) (j : ℕ) : (χ ^ j) a = 1 := by
  have hu : IsUnit a := MulChar.apply_ne_zero_iff.mp (by rw [ha]; exact one_ne_zero)
  simpa only [hu.unit_spec, ha, one_pow] using MulChar.pow_apply_coe χ j hu.unit

/-- All powers, including `j = 0`, use the same quartic character,
trace-zero point, additive character, and integer orientation. -/
theorem msxTableCorrection_pow_eq_torusSymbol
    (hc : ringChar F ≠ 2) (q4 : Fintype.card F % 4 = 1) (hm : quadraticChar F (-1) = 1)
    (h : (Ext d)ˣ) [NeZero (orderOf h)]
    (ho : orderOf h = (Fintype.card F + 1) / 2) (hn : (h : Ext d).norm = 1)
    (τ ξ : MulChar (Ext d) ℂ) (quartic : τ ^ 2 = eta (Ext d))
    (τbase : ∀ s : F, τ (algebraMap F (Ext d) s) = eta F s)
    (ξbase : ∀ s : Fˣ, ξ (algebraMap F (Ext d) (s : F)) = 1)
    (w : Ext d) (ξw : ξ w = 1) (k : Fˣ)
    (coord : twiceRoot d = algebraMap F (Ext d) (k : F) * w)
    (j : ℕ) (θ : AddChar (Fin (orderOf h)) ℂ) (spins : ∀ i, ξ (spin h i) ^ j = θ i)
    (ψ : AddChar F ℂ) (primitive : ψ.IsPrimitive) :
    msxTableCorrection τ (ξ ^ j) w ψ = 2 * (msxTableOrientation k : ℂ) * torusSymbol h θ := by
  apply msxTableCorrection_eq_torusSymbol hc q4 hm h ho hn τ (ξ ^ j) quartic τbase
    (fun s ↦ pow_on_trivial_value ξ _ (ξbase s) j) w (pow_on_trivial_value ξ w ξw j) k coord θ _ ψ primitive
  intro i
  calc
    _ = ξ (spin h i) ^ j := by
      simpa only [Units.val_pow_eq_pow_val, spin] using MulChar.pow_apply_coe ξ j (h ^ i.val)
    _ = _ := spins i

#print axioms msxTableCorrection_pow_eq_torusSymbol

end Hadamard.NonsplitTorus.MSXTable
