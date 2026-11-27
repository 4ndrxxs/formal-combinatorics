import PermanentTwenty
import Mathlib.Basic.Complex.Basic

/-! A concrete statement in standard notation over the complex numbers.
Only the polynomial identity for the proposed expression is assumed. -/

open MvPolynomial Matrix

theorem complex_five_by_five_permanent (m : ℕ)
    (A : Matrix (Fin m) (Fin m) ℂ)
    (F : Fin 5 × Fin 5 → Matrix (Fin m) (Fin m) ℂ)
    (identity :
      (Matrix.of (fun i j : Fin 5 ↦ (X (i,j) : MvPolynomial (Fin 5 × Fin 5) ℂ))).permanent =
      (MvPolynomial.C.mapMatrix A +
       ∑ s : Fin 5 × Fin 5, (X s : MvPolynomial (Fin 5 × Fin 5) ℂ) •
         MvPolynomial.C.mapMatrix (F s)).det) : 20 ≤ m := by
  have bound := PermanentFive.determinantal_lower_bound_twenty A F identity
  simpa using bound

#print axioms complex_five_by_five_permanent
