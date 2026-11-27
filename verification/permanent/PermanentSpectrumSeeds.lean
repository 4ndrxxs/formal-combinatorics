import PermanentRankCertificate

/-! Two integral points of the permanent hypersurface. Their Hessian
ranks are four and seven, and their cofactor matrices have rank one.
The seven-dimensional minor has determinant minus four. -/
noncomputable section
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000
open Matrix PermanentFive QuinticPencil
namespace PermanentBorder
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

def Marked (z : CellOf I → K) (s : ℕ) : Prop := value z=0 ∧ (cofactor z).rank=1 ∧
  (hessian (per K I) z).rank=s ∧ ∃ w : CellOf I → K, hessian (per K I) z *ᵥ w=gradAt z ∧
    gradAt z ⬝ᵥ w=0

theorem Marked.extend {z : CellOf I → K} {s : ℕ} (h : Marked z s) :
    Marked (PermanentBorder.extend z) (s+2) := by
  obtain ⟨zero,one,rank,w,image,null⟩ := h
  refine ⟨(value_extend z).trans zero,(cofactor_rank_extend z zero).trans one,?_,
    pad w,pad_preserves_witness z w zero image null⟩
  rw [hessian_rank_extend z w image null,one,rank]

def evenPoint (u : CellOf (Fin 2)) : ℤ := ![![1, 0], ![0, 0]] u.1 u.2
private def evenDirection (u : CellOf (Fin 2)) : ℤ := ![![1, 0], ![0, 0]] u.1 u.2

private def evenCofactorPick : Fin 1 → Fin 2 := ![1]
private def evenCofactorV : Matrix (Fin 1) (Fin 2) ℤ := Matrix.of fun i u ↦
  ![![0, 1]] i u
private def evenCofactorW : Matrix (Fin 1) (Fin 1) ℤ := Matrix.of fun i j ↦
  ![![1]] i j
private theorem evenCofactorCols : cofactor evenPoint=(cofactor evenPoint).submatrix id evenCofactorPick*evenCofactorV := by
  decide +kernel
private theorem evenCofactorInv : evenCofactorW*(cofactor evenPoint).submatrix evenCofactorPick evenCofactorPick=(1:ℤ) • 1 := by
  decide +kernel

private theorem evenCofactorRank : ((cofactor evenPoint).map (Int.castRingHom K)).rank=1 := by
  apply rank_certificate _ evenCofactorPick evenCofactorV evenCofactorW 1 evenCofactorCols evenCofactorInv
  norm_num

private def evenHessianPick : Fin 4 → CellOf (Fin 2) := ![(0,0), (0,1), (1,0), (1,1)]
private def evenHessianV : Matrix (Fin 4) (CellOf (Fin 2)) ℤ := Matrix.of fun i u ↦
  ![![![1, 0], ![0, 0]], ![![0, 1], ![0, 0]], ![![0, 0], ![1, 0]], ![![0, 0], ![0, 1]]] i u.1 u.2
private def evenHessianW : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of fun i j ↦
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0]] i j
private theorem evenHessianCols : table evenPoint=(table evenPoint).submatrix id evenHessianPick*evenHessianV := by
  decide +kernel
private theorem evenHessianInv : evenHessianW*(table evenPoint).submatrix evenHessianPick evenHessianPick=(1:ℤ) • 1 := by
  decide +kernel

private theorem evenHessianRank : ((table evenPoint).map (Int.castRingHom K)).rank=4 := by
  apply rank_certificate _ evenHessianPick evenHessianV evenHessianW 1 evenHessianCols evenHessianInv
  norm_num

theorem even_marked : Marked (castPoint K evenPoint) 4 := by
  have value : integralValue evenPoint=0 := by decide +kernel
  have image : table evenPoint *ᵥ evenDirection=gradAt evenPoint := by decide +kernel
  have null : gradAt evenPoint ⬝ᵥ evenDirection=0 := by decide +kernel
  refine ⟨by rw [cast_value,value,Int.cast_zero],by rw [cast_cofactor,evenCofactorRank],
    by rw [cast_hessian,evenHessianRank],castPoint K evenDirection,cast_witness _ _ image null⟩

def oddPoint (u : CellOf (Fin 3)) : ℤ := ![![0, 0, 1], ![0, 0, 1], ![1, 1, 1]] u.1 u.2
private def oddDirection (u : CellOf (Fin 3)) : ℤ := ![![0, 0, 1], ![0, 0, 1], ![0, 0, 0]] u.1 u.2

private def oddCofactorPick : Fin 1 → Fin 3 := ![0]
private def oddCofactorV : Matrix (Fin 1) (Fin 3) ℤ := Matrix.of fun i u ↦
  ![![1, 1, 0]] i u
private def oddCofactorW : Matrix (Fin 1) (Fin 1) ℤ := Matrix.of fun i j ↦
  ![![1]] i j
private theorem oddCofactorCols : cofactor oddPoint=(cofactor oddPoint).submatrix id oddCofactorPick*oddCofactorV := by
  decide +kernel
private theorem oddCofactorInv : oddCofactorW*(cofactor oddPoint).submatrix oddCofactorPick oddCofactorPick=(1:ℤ) • 1 := by
  decide +kernel

private theorem oddCofactorRank : ((cofactor oddPoint).map (Int.castRingHom K)).rank=1 := by
  apply rank_certificate _ oddCofactorPick oddCofactorV oddCofactorW 1 oddCofactorCols oddCofactorInv
  norm_num

private def oddHessianPick : Fin 7 → CellOf (Fin 3) := ![(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0)]
private def oddHessianV : Matrix (Fin 7) (CellOf (Fin 3)) ℤ := Matrix.of fun i u ↦
  ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]] i u.1 u.2
private def oddHessianW : Matrix (Fin 7) (Fin 7) ℤ := Matrix.of fun i j ↦
  ![![1, -1, 1, -1, 1, 3, -2], ![-1, 1, -1, 1, -1, 1, 2], ![1, -1, 1, 3, 1, -1, -2], ![-1, 1, 3, 1, -1, 1, -2], ![1, -1, 1, -1, 1, -1, 2], ![3, 1, -1, 1, -1, 1, -2], ![-2, 2, -2, -2, 2, -2, 4]] i j
private theorem oddHessianCols : table oddPoint=(table oddPoint).submatrix id oddHessianPick*oddHessianV := by
  decide +kernel
private theorem oddHessianInv : oddHessianW*(table oddPoint).submatrix oddHessianPick oddHessianPick=(4:ℤ) • 1 := by
  decide +kernel

private theorem oddHessianRank (two : (2:K)≠0) : ((table oddPoint).map (Int.castRingHom K)).rank=7 := by
  apply rank_certificate _ oddHessianPick oddHessianV oddHessianW 4 oddHessianCols oddHessianInv
  exact_mod_cast (show (4:K)≠0 by convert mul_ne_zero two two using 1; norm_num)

theorem odd_marked (two : (2:K)≠0) : Marked (castPoint K oddPoint) 7 := by
  have value : integralValue oddPoint=0 := by decide +kernel
  have image : table oddPoint *ᵥ oddDirection=gradAt oddPoint := by decide +kernel
  have null : gradAt oddPoint ⬝ᵥ oddDirection=0 := by decide +kernel
  refine ⟨by rw [cast_value,value,Int.cast_zero],by rw [cast_cofactor,oddCofactorRank],
    by rw [cast_hessian,oddHessianRank two],castPoint K oddDirection,cast_witness _ _ image null⟩

#print axioms even_marked
#print axioms odd_marked
end PermanentBorder
