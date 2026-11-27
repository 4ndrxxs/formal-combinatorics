import AnisotropicHyperbolicBound
import PermanentRectangleAnisotropy
import PermanentRectangleMatrices

/-! The split Gram matrix on twelve coordinates has Witt index four over the
two-variable rational function field. This file proves the upper bound on the index. -/

noncomputable section
open Matrix Module RationalSpecialization
namespace PermanentFive.Rectangle
variable {K : Type*} [Field K] [CharZero K]

private def first : Fin 4 → Fin 12 := ![0,1,2,3]
private def second : Fin 4 → Fin 12 := ![4,5,6,7]
private def last : Fin 4 → Fin 12 := ![8,9,10,11]

private def part {R : Type*} [Field R] (d : Fin 4 → Fin 12) :
    (Fin 12 → R) →ₗ[R] (Fin 4 → R) := LinearMap.pi fun i ↦ LinearMap.proj (d i)

private def cross (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  diagonal ![24,-8,-8,-8]
private def rest {R : Type*} [CommRing R] (s t : R) : Matrix (Fin 4) (Fin 4) R :=
  diagonal ![-48,-16*t,-16*s,16*s*t]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem split_pair {R : Type*} [Field R] (s t : R) (u v : Fin 12 → R) :
    (split s t).toBilin' u v =
    (cross R).toBilin' (part second u) (part first v) +
    (cross R).toBilin' (part second v) (part first u) +
    (rest s t).toBilin' (part last u) (part last v) := by
  norm_num [Matrix.toBilin'_apply,Fin.sum_univ_succ,split,cross,rest,Matrix.diagonal_apply,
    part,first,second,last]
  ring

theorem split_index_le_four (U : Submodule (Ext K) (Fin 12 → Ext K))
    (iso : U ≤ (split (paramS K) (paramT K)).toBilin'.orthogonal U) :
    finrank (Ext K) U ≤ 4 := by
  have joint (u : Fin 12 → Ext K) (a : part first u = 0) (b : part second u = 0)
      (c : part last u = 0) : u = 0 := by
    funext i
    fin_cases i <;> first
      | exact congrFun a 0 | exact congrFun a 1 | exact congrFun a 2 | exact congrFun a 3
      | exact congrFun b 0 | exact congrFun b 1 | exact congrFun b 2 | exact congrFun b 3
      | exact congrFun c 0 | exact congrFun c 1 | exact congrFun c 2 | exact congrFun c 3
  have nd : (cross (Ext K)).toBilin'.Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
    norm_num [cross,Matrix.det_diagonal,Fin.prod_univ_succ]
  have anis (u : Fin 4 → Ext K) (h : (rest (paramS K) (paramT K)).toBilin' u u = 0) : u = 0 := by
    apply four_anisotropic u
    norm_num [Matrix.toBilin'_apply,Fin.sum_univ_succ,rest,Matrix.diagonal_apply] at h
    linear_combination h
  have pair (u : Fin 12 → Ext K) (hu : u ∈ U) (v : Fin 12 → Ext K) (hv : v ∈ U) := iso hv u hu
  have h := hyperbolic_plane_bound (part first) (part second) (part last) joint
    (cross (Ext K)).toBilin' nd (rest (paramS K) (paramT K)).toBilin' anis U (by
      intro u hu v hv
      rw [← split_pair]
      exact pair u hu v hv)
  simpa using h

#print axioms split_index_le_four
end PermanentFive.Rectangle
