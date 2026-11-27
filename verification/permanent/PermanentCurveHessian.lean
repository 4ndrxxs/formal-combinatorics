import PermanentCurveCertificate
import Mathlib.Algebra.CharZero.Infinite

/-! The complementary block supplies a rank-ten Hessian test on the
explicit plane and has a nonsingular slope. -/
noncomputable section
open Polynomial Matrix Finset PermanentFive QuinticPencil
namespace PermanentCurve
variable {R S : Type*} [CommRing R] [CommRing S]

theorem same_row (z : Cell → R) (r j k : Idx) : secondAt z (r,j) (r,k) = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  unfold_projs
  split_ifs with h
  · exact False.elim (h.2.1 (p.injective (h.2.2.trans h.1.symm)))
  · rfl

variable {K : Type*} [Field K]

theorem rank_ten (z : Cell → K)
    (nz : ((hessian (per K Idx) z).submatrix lowRow highRow).det ≠ 0) :
    10 ≤ (hessian (per K Idx) z).rank := by
  let H := hessian (per K Idx) z
  let B := H.submatrix lowRow highRow
  let r : Idx ⊕ Idx → Cell := Sum.elim lowRow highRow
  let c : Idx ⊕ Idx → Cell := Sum.elim highRow lowRow
  have symm (a b : Cell) : H a b = H b a := by
    change MvPolynomial.eval _ (MvPolynomial.pderiv _ (MvPolynomial.pderiv _ _)) = _
    rw [MvPolynomial.pderiv_comm]
    rfl
  have blockEq : H.submatrix r c = Matrix.fromBlocks B 0 0 B.transpose := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · rfl
    · exact (second_formula z _ _).trans (same_row z 3 i j)
    · exact (second_formula z _ _).trans (same_row z 4 i j)
    · exact symm _ _
  have nonzero : (H.submatrix r c).det ≠ 0 := by
    rw [blockEq,Matrix.det_fromBlocks_zero₂₁,Matrix.det_transpose]
    exact mul_ne_zero nz nz
  have le := Matrix.rank_submatrix_le H r c
  rw [Matrix.rank_of_det_ne_zero nonzero] at le
  exact le

def slopePoint (x : Cell) : ℤ := slope x.1 x.2
def slopeBlock : Matrix Idx Idx ℤ :=
  !![0, -4, 0, 0, 0;
    -4, 0, 0, 0, 0;
    0, 0, 0, -4, -2;
    0, 0, -4, 0, 4;
    0, 0, -2, 4, 0]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem slope_entries (i j : Idx) :
    secondAt slopePoint (lowRow i) (highRow j) = slopeBlock i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem slope_det : slopeBlock.det = -1024 := by decide +kernel

set_option maxHeartbeats 5000000 in
theorem slope_rank (K : Type*) [Field K] [CharZero K] :
    10 ≤ (hessian (per K Idx) ((Int.castRingHom K) ∘ slopePoint)).rank := by
  apply rank_ten
  have mat : (hessian (per K Idx) ((Int.castRingHom K) ∘ slopePoint)).submatrix lowRow highRow =
      (Int.castRingHom K).mapMatrix slopeBlock := by
    ext i j
    change hessian (per K Idx) ((Int.castRingHom K) ∘ slopePoint) (lowRow i) (highRow j) =
      (Int.castRingHom K) (slopeBlock i j)
    rw [second_formula,second_map,slope_entries]
  rw [mat,←RingHom.map_det,slope_det]
  norm_num

set_option maxHeartbeats 3000000 in
theorem obstruction_expression (K : Type*) [Field K] :
    obstructionPolynomial K =
      curveP (X : (RatFunc K)[X]) + C RatFunc.X * curveQ X := by
  unfold obstructionPolynomial graph
  have p := map_curveP (Polynomial.mapRingHom (RatFunc.C : K →+* RatFunc K)) (X : K[X])
  have q := map_curveQ (Polynomial.mapRingHom (RatFunc.C : K →+* RatFunc K)) (X : K[X])
  simpa only [Polynomial.coe_mapRingHom,Polynomial.map_X] using congrArg₂
    (fun x y : (RatFunc K)[X] ↦ x+C RatFunc.X*y) p q

def actualMatrix (t u : R) : Matrix Idx Idx R := Matrix.of (actual t u)

theorem actual_det_map (f : R →+* S) (t u : R) :
    f (actualMatrix t u).det = (actualMatrix (f t) (f u)).det := by
  rw [f.map_det]
  congr 1
  ext i j
  exact actual_map f t u i j

theorem actual_det_eq_rhs [CharZero K] (t u : K) : (actualMatrix t u).det = rhs t u := by
  have m : actualMatrix t u = block t u := by ext i j; exact actual_block _ _ _ _
  rw [m,block_det]

theorem polynomial_actual [CharZero K] (t u : K[X]) : (actualMatrix t u).det = rhs t u := by
  let g := algebraMap K[X] (RatFunc K)
  let _ : CharZero (RatFunc K) := charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  apply IsFractionRing.injective K[X] (RatFunc K)
  exact (actual_det_map g t u).trans ((actual_det_eq_rhs (g t) (g u)).trans (rhs_map g t u).symm)

theorem hessian_curve_polynomial (K : Type*) [Field K] [CharZero K] :
    (actualMatrix (X : (RatFunc K)[X]) (C RatFunc.X)).det =
      64 * obstructionPolynomial K := by
  let _ : CharZero (RatFunc K) := charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  rw [obstruction_expression]
  exact polynomial_actual (X : (RatFunc K)[X]) (C RatFunc.X)

#print axioms hessian_curve_polynomial
#print axioms slope_rank
end PermanentCurve
