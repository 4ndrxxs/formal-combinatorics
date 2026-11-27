import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Ring

/-! A mixed second coefficient of a regular affine determinantal pencil.
Three formal variables record the line through the base point and two
independent directional perturbations. -/

noncomputable section
open Matrix PowerSeries

namespace QuinticPencil

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The matrix of formal geometric series for a constant transfer matrix. -/
def geometric (D : Matrix ι ι R) : Matrix ι ι R⟦X⟧ :=
  Matrix.of fun i j ↦ PowerSeries.mk fun d ↦ (D ^ d) i j

/-- The lower right block on the line through the common endpoint kernel. -/
def lineBlock (D : Matrix ι ι R) : Matrix ι ι R⟦X⟧ :=
  1 - (PowerSeries.X : R⟦X⟧) • PowerSeries.C.mapMatrix D

theorem lineBlock_mul_geometric (D : Matrix ι ι R) : lineBlock D * geometric D = 1 := by
  have recur : geometric D = 1 + (PowerSeries.X : R⟦X⟧) •
      (PowerSeries.C.mapMatrix D * geometric D) := by
    ext i j d
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, geometric, Matrix.of_apply,
      PowerSeries.coeff_mk, map_add]
    cases d with
    | zero =>
      by_cases h : i = j <;> simp [h, Matrix.one_apply, coeff_zero_eq_constantCoeff_apply]
    | succ d =>
      rw [PowerSeries.coeff_succ_X_mul, Matrix.mul_apply, map_sum]
      simp only [pow_succ' D, Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
      by_cases h : i = j <;> simp [h, Matrix.one_apply, PowerSeries.coeff_one]
  rw [lineBlock, sub_mul, Matrix.one_mul, Matrix.smul_mul, sub_eq_iff_eq_add]
  exact recur

theorem lineBlock_constant (D : Matrix ι ι R) : constantCoeff (lineBlock D).det = 1 := by
  have h : (constantCoeff (R := R)).mapMatrix (lineBlock D) = 1 := by
    ext i j
    by_cases he : i = j <;> simp [lineBlock, RingHom.mapMatrix_apply, Matrix.one_apply, he]
  rw [RingHom.map_det, h, Matrix.det_one]

abbrev MixedSeries (R : Type*) [CommRing R] := (R⟦X⟧)⟦X⟧

/-- Evaluation of both auxiliary power series variables at zero. -/
def base (R : Type*) [CommRing R] : MixedSeries R →+* R :=
  (constantCoeff (R := R)).comp (constantCoeff (R := R⟦X⟧))

/-- Coefficient of the product of the two auxiliary variables. -/
def mixed (R : Type*) [CommRing R] : MixedSeries R →+ R :=
  (PowerSeries.coeff (R := R) 1).toAddMonoidHom.comp
    (PowerSeries.coeff (R := R⟦X⟧) 1).toAddMonoidHom

/-- The linear polynomial with specified coefficients in the two variables. -/
def edge (a b : R) : MixedSeries R := C (X * C a) + X * C (C b)

theorem mixed_product (g t : MixedSeries R) (a b c d : R) :
    mixed R (g * (edge a b * t * edge c d)) =
      base R g * (base R t * (a * d + b * c)) := by
  change (coeff (R := R) 1) ((coeff (R := R⟦X⟧) 1) (g * (edge a b * t * edge c d))) =
    constantCoeff (constantCoeff g) *
    (constantCoeff (constantCoeff t) * (a * d + b * c))
  simp [edge, PowerSeries.coeff_one_mul]
  ring

/-- The determinant of a bordered matrix over two independent infinitesimals. -/
def border (u v w x : ι → R) (T : Matrix ι ι (MixedSeries R)) :=
  Matrix.fromBlocks (0 : Matrix Unit Unit (MixedSeries R))
    (-(Matrix.of fun (_ : Unit) i ↦ edge (u i) (v i)))
    (Matrix.of fun j (_ : Unit) ↦ edge (w j) (x j)) T

theorem mixed_border (u v w x : ι → R) (T : Matrix ι ι (MixedSeries R))
    (Q : Matrix ι ι R) (inv : (base R).mapMatrix T * Q = 1) :
    mixed R (border u v w x T).det = ((base R).mapMatrix T).det *
      ∑ j, ∑ i, Q i j * (u i * x j + v i * w j) := by
  have hunit : IsUnit T := by
    apply (Matrix.isUnit_iff_isUnit_det T).mpr
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    change IsUnit (base R T.det)
    rw [RingHom.map_det]
    let _ := Matrix.detInvertibleOfRightInverse _ _ inv
    exact isUnit_of_invertible _
  let _ : Invertible T := hunit.invertible
  have left : (base R).mapMatrix (⅟T) * (base R).mapMatrix T = 1 := by
    rw [← map_mul, invOf_mul_self, map_one]
  have agree : (base R).mapMatrix (⅟T) = Q := by
    calc
      _ = (base R).mapMatrix (⅟T) * ((base R).mapMatrix T * Q) := by rw [inv, mul_one]
      _ = Q := by rw [← mul_assoc, left, one_mul]
  have entry (i j : ι) : base R ((⅟T) i j) = Q i j :=
    congrArg (fun A : Matrix ι ι R ↦ A i j) agree
  rw [border, Matrix.det_fromBlocks₂₂, Matrix.neg_mul, Matrix.neg_mul,
    zero_sub, neg_neg, Matrix.det_unique (n := Unit), Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum, map_sum,
    mixed_product, entry, RingHom.map_det]


/-- The mixed derivative of the bordered determinant is the determinant of the
line block times the formal series of all transfer-matrix moments. Only the
restriction of the lower block to the line enters the answer. -/
theorem mixed_line (D : Matrix ι ι R) (u v w x : ι → R)
    (T : Matrix ι ι (MixedSeries R⟦X⟧)) (line : (base R⟦X⟧).mapMatrix T = lineBlock D) :
    mixed R⟦X⟧ (border (C ∘ u) (C ∘ v) (C ∘ w) (C ∘ x) T).det =
      (lineBlock D).det * PowerSeries.mk (fun d ↦
        ∑ j, ∑ i, (D^d) i j * (u i * x j + v i * w j)) := by
  have inv : (base R⟦X⟧).mapMatrix T * geometric D = 1 := by
    rw [line, lineBlock_mul_geometric]
  rw [mixed_border _ _ _ _ T (geometric D) inv, line]
  congr 1
  ext n
  simp only [map_sum, PowerSeries.coeff_mk, Function.comp_apply, ← map_mul, ← map_add,
    geometric, Matrix.of_apply, PowerSeries.coeff_mul_C]

#print axioms mixed_line

#print axioms lineBlock_mul_geometric
#print axioms lineBlock_constant
#print axioms mixed_border

end QuinticPencil
