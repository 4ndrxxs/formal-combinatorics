import MSXTableGaussFactor
import MSXTableCyclic
import MSXTableJacobi
import MSXTableParameters

/-! The original three determinant values in Momihara–Suda–Xiang,
Theorem 1.6, rows (4), (5), and (6), as referenced in Problem 15 of
Egan, Kotsireas, London and Ó Catháin. -/

noncomputable section
open Finset Hadamard.LinPhoa Hadamard.NonsplitTorus Hadamard.NonsplitTorus.MSXTable
open scoped ComplexOrder

namespace Hadamard.MSXProblem15

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {d : F} [Fact (¬ IsSquare d)]

private noncomputable local instance (d : F) : Fintype (Ext d) :=
  Fintype.ofEquiv (F × F) (QuadraticAlgebra.equivProd d 0).symm

private noncomputable local instance (h : (Ext d)ˣ) : NeZero (orderOf h) :=
  ⟨(orderOf_pos h).ne'⟩

/-- The right side of the original determinant table's row (4).
The range starts at zero and includes the index `(q-1)/2`. -/
def classFour (ω : (Ext d)ˣ) (τ ν : MulChar (Ext d) ℂ) (ψ : AddChar F ℂ) : ℂ :=
  let q := Fintype.card F
  ∏ j ∈ range ((q-1)/2+1), ((q:ℂ)+1 -
    gaussSum (eta F) ψ / (q:ℂ) *
      ∑ ℓ ∈ ({1,3}:Finset ℕ), gaussSum (τ^ℓ * ν^j) (traceCharacter ψ) *
        (τ^ℓ)⁻¹ ((ω : Ext d)^((q+1)/2)))

/-- The right side of the original determinant table's row (5). -/
def classFive (χ : MulChar F ℂ) : ℂ :=
  let q := Fintype.card F
  let η := eta F
  ((q:ℂ)-1)^2 * ∏ j ∈ Icc 1 ((q-3)/2),
    ((q:ℂ)+1 + jacobiSum (η*χ^j) η + jacobiSum (χ^j) η)

/-- The right side of the original determinant table's row (6). -/
def classSix (χ : MulChar F ℂ) : ℂ :=
  let q := Fintype.card F
  let η := eta F
  ((q:ℂ)^2+2*(q:ℂ)+5) * ∏ j ∈ Icc 1 ((q-3)/2),
    ((q:ℂ)+1 - jacobiSum (η*χ^j) η - jacobiSum (χ^j) η)

/-- Four fifths of the Ehlich–Wojtas bound at order q+1 for odd q. -/
def threshold (q : ℕ) : ℝ := (4/5)*(2*(q:ℝ))*((q:ℝ)-1)^(q/2)

omit [Fact (¬ IsSquare d)] in
private theorem classFour_modes (q4 : Fintype.card F%4=1) (ω : (Ext d)ˣ)
    (τ ν : MulChar (Ext d) ℂ) (ψ : AddChar F ℂ) :
    classFour ω τ ν ψ = ∏ j : Fin ((Fintype.card F+1)/2),
      ((Fintype.card F:ℂ)+1-msxTableCorrection τ (ν^j.val) (phasePoint ω) ψ) := by
  classical
  have size : (Fintype.card F-1)/2+1 = (Fintype.card F+1)/2 := by omega
  unfold classFour
  dsimp only
  rw [size, Fin.prod_univ_eq_prod_range (fun j : ℕ ↦ (Fintype.card F:ℂ)+1-
    msxTableCorrection τ (ν^j) (phasePoint ω) ψ) ((Fintype.card F+1)/2)]
  apply prod_congr rfl
  intro j _
  simp [msxTableCorrection, phasePoint]

private theorem row_four_with_coordinates
    (q4 : Fintype.card F%4=1) (lo : 29 ≤ Fintype.card F)
    (ω : (Ext d)ˣ) (hω : orderOf ω = Nat.card (Ext d)ˣ)
    (τ ν : MulChar (Ext d) ℂ) (hν : orderOf ν = (Fintype.card F+1)/2)
    (quartic : τ^2 = eta (Ext d))
    (τbase : ∀ s : F, τ (algebraMap F (Ext d) s) = eta F s)
    (k : Fˣ) (coord : twiceRoot d = algebraMap F (Ext d) (k:F) * phasePoint ω)
    (ψ : AddChar F ℂ) (prim : ψ.IsPrimitive) :
    (threshold (Fintype.card F) : ℂ) ≤ classFour ω τ ν ψ := by
  classical
  let h := torusGen ω
  have ho := torusGen_order q4 ω hω
  have hn := torusGen_norm ω
  have hc : ringChar F ≠ 2 := by
    intro e
    have even := FiniteField.even_card_of_char_two e
    omega
  have hm : quadraticChar F (-1) = 1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
      (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  let α := -(msxTableOrientation k)
  have sign : α^2 = 1 := by simpa only [α,neg_sq] using msxTableOrientation_sq k
  let e := modeEquiv q4 ω hω ν hν
  let f := fun θ : AddChar (Fin (orderOf h)) ℂ ↦
    (Fintype.card F:ℂ)+1+2*(α:ℂ)*torusSymbol h θ
  have factors (j : Fin ((Fintype.card F+1)/2)) :
      (Fintype.card F:ℂ)+1-msxTableCorrection τ (ν^j.val) (phasePoint ω) ψ = f (e j) := by
    rw [msxTableCorrection_pow_eq_torusSymbol hc q4 hm h ho hn τ ν quartic τbase
      (indexChar_base q4 ν hν) (phasePoint ω) (indexChar_phase ω ν hν) k coord j.val (e j)
      (fun i ↦ (modeEquiv_apply q4 ω hω ν hν j i).symm) ψ prim]
    dsimp only [f,α]
    push_cast
    ring
  have result : classFour ω τ ν ψ = ((|(twoCirculant h α).det|:ℝ):ℂ) := by
    rw [classFour_modes q4,torus_character_product hc q4 hm h ho hn α sign]
    exact (prod_congr rfl fun j _ ↦ factors j).trans (e.prod_comp f)
  rw [result,Complex.real_le_real]
  exact torus_four_fifths q4 lo h ho hn α sign

/-- The quartic and odd characters are only required to have the orders
specified in the published formula. The base additive character is arbitrary
and primitive. -/
theorem row_four (q4 : Fintype.card F%4=1) (lo : 29 ≤ Fintype.card F)
    (ω : (Ext d)ˣ) (hω : orderOf ω = Nat.card (Ext d)ˣ)
    (τ ν : MulChar (Ext d) ℂ) (hτ : orderOf τ = 4)
    (hν : orderOf ν = (Fintype.card F+1)/2)
    (ψ : AddChar F ℂ) (prim : ψ.IsPrimitive) :
    (threshold (Fintype.card F) : ℂ) ≤ classFour ω τ ν ψ := by
  obtain ⟨k,coord⟩ := phasePoint_coordinate q4 ω hω
  exact row_four_with_coordinates q4 lo ω hω τ ν hν (quartic_square q4 ω hω τ hτ)
    (quartic_base q4 ω hω τ hτ) k coord ψ prim

/-- Standard Ehlich–Wojtas bound, expressed as a function of matrix order. -/
def ehlichWojtas (n : ℕ) : ℝ := (2*(n:ℝ)-2)*((n:ℝ)-2)^((n-2)/2)

theorem threshold_at_order {q : ℕ} (q4 : q%4=1) :
    threshold q = (4/5:ℝ)*ehlichWojtas (q+1) := by
  have ep : (q+1-2)/2 = q/2 := by omega
  simp only [threshold,ehlichWojtas,ep,Nat.cast_add,Nat.cast_one]
  rw [show (q:ℝ)+1-2=(q:ℝ)-1 by ring]
  ring

/-- Problem 15, simultaneously for every parameter permitted in the three
published determinant products. The order on the complex numbers expresses
the real inequality and the vanishing of the imaginary part. -/
theorem problem15 (q4 : Fintype.card F%4=1) (lo : 29 ≤ Fintype.card F)
    (ω : (Ext d)ˣ) (hω : orderOf ω = Nat.card (Ext d)ˣ)
    (τ ν : MulChar (Ext d) ℂ) (hτ : orderOf τ = 4)
    (hν : orderOf ν = (Fintype.card F+1)/2)
    (χ : MulChar F ℂ) (hχ : orderOf χ = Fintype.card F-1)
    (ψ : AddChar F ℂ) (prim : ψ.IsPrimitive) :
    let B : ℂ := ((4/5:ℝ)*ehlichWojtas (Fintype.card F+1) : ℝ)
    B ≤ classFour ω τ ν ψ ∧ B ≤ classFive χ ∧ B ≤ classSix χ := by
  dsimp only
  rw [←threshold_at_order q4]
  have split := msx_table_rows_five_six q4 lo χ hχ
  have bridge : (threshold (Fintype.card F):ℂ) =
      (4/5:ℂ)*(2*(Fintype.card F:ℂ))*((Fintype.card F:ℂ)-1)^(Fintype.card F/2) := by
    simp [threshold]
  refine ⟨row_four q4 lo ω hω τ ν hτ hν ψ prim, ?_⟩
  rw [bridge]
  exact split

/-- At the order of every finite field the parameter choices are inhabited
and give all three bounds simultaneously. -/
theorem witnesses_at_field_order (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (q4 : Fintype.card F%4=1) (lo : 29≤Fintype.card F) :
    ∃ d : F, ∃ ns : ¬ IsSquare d, letI : Fact (¬ IsSquare d) := ⟨ns⟩
      ∃ ω : (Ext d)ˣ, ∃ τ ν : MulChar (Ext d) ℂ, ∃ χ : MulChar F ℂ,
      ∃ ψ : AddChar F ℂ,
      orderOf ω = Nat.card (Ext d)ˣ ∧ orderOf τ = 4 ∧ orderOf ν = (Fintype.card F+1)/2 ∧
      orderOf χ = Fintype.card F-1 ∧ ψ.IsPrimitive ∧
      let B : ℂ := ((4/5:ℝ)*ehlichWojtas (Fintype.card F+1) : ℝ)
      B ≤ classFour ω τ ν ψ ∧ B ≤ classFive χ ∧ B ≤ classSix χ := by
  obtain ⟨⟨χ,hχ⟩,⟨ψ,hψ⟩,d,ns,choices⟩ := exists_table_parameters F q4 lo
  refine ⟨d,ns,?_⟩
  let : Fact (¬ IsSquare d) := ⟨ns⟩
  obtain ⟨⟨ω,hω⟩,⟨τ,hτ⟩,ν,hν⟩ := choices
  exact ⟨ω,τ,ν,χ,ψ,hω,hτ,hν,hχ,hψ,problem15 q4 lo ω hω τ ν hτ hν χ hχ ψ hψ⟩

/-- Every admissible numerical order has a finite field and actual parameters
attaining the simultaneous three inequalities. -/
theorem every_eligible_order (q : ℕ) (pp : IsPrimePow q) (q4 : q%4=1) (lo : 29≤q) :
    ∃ (F : Type) (field : Field F) (finite : Fintype F) (dec : DecidableEq F),
      letI : Field F := field
      letI : Fintype F := finite
      letI : DecidableEq F := dec
      Fintype.card F = q ∧
      ∃ d : F, ∃ ns : ¬ IsSquare d, letI : Fact (¬ IsSquare d) := ⟨ns⟩
        ∃ ω : (Ext d)ˣ, ∃ τ ν : MulChar (Ext d) ℂ, ∃ χ : MulChar F ℂ,
        ∃ ψ : AddChar F ℂ,
        orderOf ω = Nat.card (Ext d)ˣ ∧ orderOf τ = 4 ∧ orderOf ν = (q+1)/2 ∧
        orderOf χ = q-1 ∧ ψ.IsPrimitive ∧
        let B : ℂ := ((4/5:ℝ)*ehlichWojtas (q+1) : ℝ)
        B ≤ classFour ω τ ν ψ ∧ B ≤ classFive χ ∧ B ≤ classSix χ := by
  classical
  obtain ⟨p,e,hp,he,peq⟩ := pp
  let : Fact p.Prime := ⟨hp.nat_prime⟩
  let F := GaloisField p e
  let : Fintype F := Fintype.ofFinite F
  have card : Fintype.card F = q := Fintype.card_eq_nat_card.trans ((GaloisField.card p e he.ne').trans peq)
  refine ⟨F,inferInstance,inferInstance,Classical.decEq F,card,?_⟩
  simpa only [card] using witnesses_at_field_order F (by simpa only [card] using q4)
    (by simpa only [card] using lo)

#print axioms problem15
#print axioms every_eligible_order

end Hadamard.MSXProblem15
