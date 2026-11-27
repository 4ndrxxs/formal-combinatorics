import PermanentEndpointInterval
import Mathlib.Basic.Complex.Basic

/-! Endpoint dimension and endpoint rank for every affine twenty-one by
twenty-one expression for the complex five-by-five permanent. -/
open MvPolynomial Matrix Module QuinticPencil PermanentFive

theorem complex_twenty_one_endpoint_interval
    (A : Matrix (Fin 21) (Fin 21) ℂ) (F : Fin 5 × Fin 5 → Matrix (Fin 21) (Fin 21) ℂ)
    (identity :
      (Matrix.of (fun i j : Fin 5 ↦ (X (i,j) : MvPolynomial (Fin 5 × Fin 5) ℂ))).permanent =
      (MvPolynomial.C.mapMatrix A +
       ∑ s : Fin 5 × Fin 5, (X s : MvPolynomial (Fin 5 × Fin 5) ℂ) •
         MvPolynomial.C.mapMatrix (F s)).det) :
    ∃ (b c : Fin A.rank → Cell → ℂ) (D : Fin A.rank → Fin A.rank → Cell → ℂ),
      per ℂ Idx = regularDet b c D ∧
      (5 ≤ finrank ℂ (endpoints b c).ker ∧ finrank ℂ (endpoints b c).ker ≤ 11) ∧
      (14 ≤ finrank ℂ (endpoints b c).range ∧ finrank ℂ (endpoints b c).range ≤ 20) :=
  affine_endpoint_interval A F identity (by decide)

#print axioms complex_twenty_one_endpoint_interval
