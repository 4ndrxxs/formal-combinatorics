import PermanentCurveHessian
import PermanentShapeBoards
import Mathlib.RingTheory.AdjoinRoot

/-! Every closed point of degree at most fourteen on the test line has
Hessian rank at least ten. The leading coordinates give the same bound. -/
noncomputable section
open Matrix Polynomial PermanentFive QuinticPencil
namespace PermanentCurve
set_option maxRecDepth 12000 in
private theorem support_data : ∀ u : Cell, u ∉ shapeModel 11 →
    base u.1 u.2 = 0 ∧ slope u.1 u.2=0 ∧ u ≠ (2,0) := by decide +kernel
variable {K R : Type*} [Field K] [CommRing R]

theorem plane_support (t u : R) (x : Cell) (h : x ∉ shapeModel 11) : plane t u x=0 := by
  obtain ⟨a,b,c⟩ := support_data x h
  simp [plane,a,b,c]

theorem slope_support (x : Cell) (h : x ∉ shapeModel 11) :
    (slopePoint x : R)=0 := by
  simp [slopePoint,(support_data x h).2.1]

theorem top_coordinate (u : K) (x : Cell) :
    PencilWeight.Top (plane (X : K[X]) (C u) x) 1 ((slopePoint x : ℤ) : K) := by
  have lift (n : ℤ) : (n : K[X]) = C (n : K) := (map_intCast (C : K →+* K[X]) n).symm
  unfold plane slopePoint
  rw [lift, lift]
  by_cases eq : x=(2,0) <;> simp only [eq,ite_true,ite_false,add_zero]
  all_goals constructor
  all_goals compute_degree

variable (K : Type*) [Field K] [CharZero K]
theorem prime_rank (p : (RatFunc K)[X]) (hp : Irreducible p) [Fact (Irreducible p)]
    (deg : p.natDegree ≤ 14) :
    10 ≤ (hessian (per (AdjoinRoot p) Idx)
      (plane (AdjoinRoot.mk p X) (AdjoinRoot.mk p (C RatFunc.X)))).rank := by
  let _ : CharZero (RatFunc K) := charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  let _ : CharZero (AdjoinRoot p) := charZero_of_injective_algebraMap (algebraMap (RatFunc K) (AdjoinRoot p)).injective
  let g := AdjoinRoot.mk p
  have nz : g (obstructionPolynomial K) ≠ 0 := by
    intro z
    have dvd : p ∣ obstructionPolynomial K := AdjoinRoot.mk_eq_zero.mp z
    have assoc := hp.associated_of_dvd (obstruction_irreducible K) dvd
    have le := natDegree_le_of_dvd assoc.symm.dvd hp.ne_zero
    rw [obstruction_degree] at le
    omega
  have eq : rhs (X : (RatFunc K)[X]) (C RatFunc.X) = 64 * obstructionPolynomial K := by
    rw [obstruction_expression]
    rfl
  apply rank_ten
  rw [hessian_block_det,←rhs_map,eq,map_mul]
  apply mul_ne_zero _ nz
  rw [map_ofNat]
  norm_num

#print axioms top_coordinate
#print axioms prime_rank
end PermanentCurve
