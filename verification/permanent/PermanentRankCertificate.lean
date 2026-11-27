import PermanentHessianSuspension

/-! Integer rank certificates transported to arbitrary fields. -/
noncomputable section
open Matrix Module Equiv Finset MvPolynomial PermanentFive QuinticPencil
namespace PermanentBorder
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem rank_certificate {k : ℕ} (A : Matrix I I ℤ) (pick : Fin k → I)
    (V : Matrix (Fin k) I ℤ) (W : Matrix (Fin k) (Fin k) ℤ) (d : ℤ)
    (full : A=A.submatrix id pick*V) (minor : W*A.submatrix pick pick=d • 1)
    (nz : (d:K)≠0) : (A.map (Int.castRingHom K)).rank=k := by
  let f := Int.castRingHom K
  let B := A.map f
  have allCols : B=B.submatrix id pick*V.map f := by
    change A.map f=(A.submatrix id pick).map f*V.map f
    rw [← Matrix.map_mul,←full]
  have inv : W.map f*B.submatrix pick pick=(d:K) • 1 := by
    change W.map f*(A.submatrix pick pick).map f=(d:K) • 1
    rw [←Matrix.map_mul,minor]
    ext i j
    by_cases eq : i=j <;> simp [Matrix.smul_apply,Matrix.intCast_apply,eq,f]
  have top : B.rank≤k := by
    conv_lhs => rw [allCols]
    exact (Matrix.rank_mul_le_left _ _).trans (by simpa only [Fintype.card_fin] using Matrix.rank_le_card_width (B.submatrix id pick))
  have unitRank : ((d:K) • (1:Matrix (Fin k) (Fin k) K)).rank=k := by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors 1 (mem_nonZeroDivisors_of_ne_zero nz),
      Matrix.rank_one,Fintype.card_fin]
  refine le_antisymm top ?_
  calc k=((d:K) • (1:Matrix (Fin k) (Fin k) K)).rank := unitRank.symm
       _=(W.map f*B.submatrix pick pick).rank := congrArg Matrix.rank inv.symm
       _≤(B.submatrix pick pick).rank := Matrix.rank_mul_le_right _ _
       _≤B.rank := Matrix.rank_submatrix_le B pick pick

def table (z : CellOf I → ℤ) : Matrix (CellOf I) (CellOf I) ℤ := Matrix.of (secondAt z)
def integralValue (z : CellOf I → ℤ) := (Matrix.of fun i j ↦ z (i,j)).permanent
def castPoint (K : Type*) [Field K] (z : CellOf I → ℤ) := (Int.castRingHom K) ∘ z

theorem cast_hessian (z : CellOf I → ℤ) : hessian (per K I) (castPoint K z)=
    (table z).map (Int.castRingHom K) := by
  ext i j
  rw [second_formula,castPoint,second_map]
  rfl

theorem cast_cofactor (z : CellOf I → ℤ) : cofactor (castPoint K z)=
    (cofactor z).map (Int.castRingHom K) := by
  ext i j
  exact grad_map _ _ _

theorem cast_value (z : CellOf I → ℤ) : value (castPoint K z)=(integralValue z:K) := by
  simp [value,per,Matrix.permanent,PermanentCuts.generic,castPoint,integralValue]

theorem cast_witness (z w : CellOf I → ℤ) (image : table z *ᵥ w=gradAt z) (null : gradAt z ⬝ᵥ w=0) :
    hessian (per K I) (castPoint K z) *ᵥ castPoint K w=gradAt (castPoint K z) ∧
      gradAt (castPoint K z) ⬝ᵥ castPoint K w=0 := by
  let f := Int.castRingHom K
  have g : gradAt (castPoint K z)=f ∘ gradAt z := funext (grad_map _ _)
  rw [g,cast_hessian]
  constructor
  · funext i
    exact (f.map_mulVec (table z) w i).symm.trans (congrArg f (congrFun image i))
  · change (f ∘ gradAt z) ⬝ᵥ (f ∘ w)=0
    rw [←RingHom.map_dotProduct,null,map_zero]

#print axioms rank_certificate
end PermanentBorder
