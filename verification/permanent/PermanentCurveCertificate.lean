import PermanentCurveCubicTable
import PermanentCurveDetTable
noncomputable section
open Polynomial Matrix Finset PermanentFive
namespace PermanentCurve
variable {K : Type*} [Field K] [CharZero K]

theorem actual_block (t u : K) (i j : Idx) : actual t u i j = block t u i j := by
  have checked (a b : Fin 4) : actual (a.val : K) (b.val : K) i j = block (a.val : K) (b.val : K) i j := by
    have h := congrArg (Int.castRingHom K) (cubic_table a b i j)
    simpa only [actual_map,block_entry_map,map_natCast] using h
  have fixed (b : Fin 4) (x : K) : actual x (b.val : K) i j = block x (b.val : K) i j := by
    have e := grid_eq (d:=3) (actual X (C (b.val : K)) i j) (block X (C (b.val : K)) i j)
      (actual_degree _ _ (by simp) (by simp) _ _) (block_degree _ _ (by simp) (by simp) _ _)
      (fun a ↦ by simpa only [actual_eval,block_eval,eval_X,eval_C] using checked a b)
    simpa only [actual_eval,block_eval,eval_X,eval_C] using congrArg (Polynomial.eval x) e
  have e := grid_eq (d:=3) (actual (C t) X i j) (block (C t) X i j)
    (actual_degree _ _ (by simp) (by simp) _ _) (block_degree _ _ (by simp) (by simp) _ _)
    (fun b ↦ by simpa only [actual_eval,block_eval,eval_X,eval_C] using fixed b t)
  simpa only [actual_eval,block_eval,eval_X,eval_C] using congrArg (Polynomial.eval u) e

theorem block_det (t u : K) : (block t u).det = rhs t u := by
  have checked (a b : Fin 16) : (block (a.val : K) (b.val : K)).det = rhs (a.val : K) (b.val : K) := by
    have h := congrArg (Int.castRingHom K) (determinant_table a b)
    simpa only [det_block_map,rhs_map,map_natCast] using h
  have fixed (b : Fin 16) (x : K) : (block x (b.val : K)).det = rhs x (b.val : K) := by
    have e := grid_eq (d:=15) (block X (C (b.val : K))).det (rhs X (C (b.val : K)))
      (block_det_degree _ _ (by simp) (by simp)) (rhs_degree _ _ (by simp) (by simp))
      (fun a ↦ by simpa only [block_det_eval,rhs_eval,eval_X,eval_C] using checked a b)
    simpa only [block_det_eval,rhs_eval,eval_X,eval_C] using congrArg (Polynomial.eval x) e
  have e := grid_eq (d:=15) (block (C t) X).det (rhs (C t) X)
    (block_det_degree _ _ (by simp) (by simp)) (rhs_degree _ _ (by simp) (by simp))
    (fun b ↦ by simpa only [block_det_eval,rhs_eval,eval_X,eval_C] using fixed b t)
  simpa only [block_det_eval,rhs_eval,eval_X,eval_C] using congrArg (Polynomial.eval u) e

theorem hessian_block_det (t u : K) :
    ((QuinticPencil.hessian (per K Idx) (plane t u)).submatrix lowRow highRow).det = rhs t u := by
  have eq : (QuinticPencil.hessian (per K Idx) (plane t u)).submatrix lowRow highRow = block t u := by
    ext i j
    exact (second_formula (plane t u) _ _).trans (actual_block t u i j)
  rw [eq,block_det]

#print axioms hessian_block_det
end PermanentCurve
