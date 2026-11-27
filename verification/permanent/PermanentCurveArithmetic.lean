import PermanentCurvePlane
import PermanentCurvePolynomials
import PencilPolynomialWeights

/-! Exact identification of the complementary Hessian determinant with the
irreducible degree-fifteen polynomial. Finite integer evaluations are
lifted by interpolation over any characteristic-zero field. -/
noncomputable section
open Polynomial Matrix Finset PermanentFive
namespace PermanentCurve
variable {R S : Type*} [CommRing R] [CommRing S]

theorem block_entry_map (f : R →+* S) (t u : R) (i j : Idx) :
    f (block t u i j) = block (f t) (f u) i j :=
  congrFun (congrFun (block_map f t u) i) j

theorem det_block_map (f : R →+* S) (t u : R) :
    f (block t u).det = (block (f t) (f u)).det := by
  rw [f.map_det]
  exact congrArg Matrix.det (block_map f t u)

def rhs (t u : R) : R := 64*(curveP t+u*curveQ t)

theorem rhs_map (f : R →+* S) (t u : R) : f (rhs t u) = rhs (f t) (f u) := by
  simp only [rhs,map_mul,map_add,map_curveP,map_curveQ,map_ofNat]

theorem block_det_degree (t u : R[X]) (ht : t.natDegree ≤ 1) (hu : u.natDegree ≤ 1) :
    (block t u).det.natDegree ≤ 15 := by
  let M := block t u
  let N : Matrix Idx Idx R := fun i j ↦ (M i j).coeff 3
  have d := (PencilWeight.top_det M (fun _ ↦ 3) N (fun i j ↦ ⟨block_degree t u ht hu i j,rfl⟩)).1
  simpa [Idx,M] using d

theorem rhs_degree (t u : R[X]) (ht : t.natDegree ≤ 1) (hu : u.natDegree ≤ 1) :
    (rhs t u).natDegree ≤ 15 := by
  unfold rhs curveP curveQ
  compute_degree; omega

theorem actual_eval (x : R) (t u : R[X]) (i j : Idx) :
    (actual t u i j).eval x = actual (t.eval x) (u.eval x) i j :=
  actual_map (evalRingHom x) t u i j

theorem block_eval (x : R) (t u : R[X]) (i j : Idx) :
    (block t u i j).eval x = block (t.eval x) (u.eval x) i j :=
  block_entry_map (evalRingHom x) t u i j

theorem block_det_eval (x : R) (t u : R[X]) :
    (block t u).det.eval x = (block (t.eval x) (u.eval x)).det :=
  det_block_map (evalRingHom x) t u

theorem rhs_eval (x : R) (t u : R[X]) :
    (rhs t u).eval x = rhs (t.eval x) (u.eval x) :=
  rhs_map (evalRingHom x) t u

end PermanentCurve
