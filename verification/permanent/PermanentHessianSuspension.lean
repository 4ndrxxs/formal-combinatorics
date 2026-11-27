import PermanentBorderRank
import PermanentHessianSymmetry

/-! The bordered Hessian gains exactly twice the rank of the cofactor
matrix when the permanent vanishes and the gradient is represented
by an isotropic vector for the Hessian. These conditions persist after
the border, so the construction can be iterated in every characteristic. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial PermanentFive QuinticPencil
namespace PermanentBorder
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

def sideIndex (I : Type*) : I ⊕ Unit ≃ Option I where
  toFun := Sum.elim some (fun _ ↦ none)
  invFun | some i => Sum.inl i | none => Sum.inr ()
  left_inv := by rintro (i|⟨⟩) <;> rfl
  right_inv := by rintro (_|i) <;> rfl

def borderIndex (I : Type*) : ((CellOf I ⊕ Unit) ⊕ (I ⊕ I)) ≃ Bigger I where
  toFun := Sum.elim (Sum.elim old (fun _ ↦ corner)) (Sum.elim left right)
  invFun
    | (some r,some j) => Sum.inl (Sum.inl (r,j))
    | (none,none) => Sum.inl (Sum.inr ())
    | (some r,none) => Sum.inr (Sum.inl r)
    | (none,some j) => Sum.inr (Sum.inr j)
  left_inv := by rintro ((⟨r,j⟩|⟨⟩)|(r|j)) <;> rfl
  right_inv := by rintro ⟨_|r,_|j⟩ <;> rfl

theorem grad_extend_zero (z : CellOf I → K) (zero : value z=0) :
    gradAt (extend z)=pad (gradAt z) := by
  funext u
  simp [grad_extend,zero]

theorem cofactor_rank_extend (z : CellOf I → K) (zero : value z=0) :
    (cofactor (extend z)).rank=(cofactor z).rank := by
  let e := sideIndex I
  have eq : (cofactor (extend z)).submatrix e e=
      Matrix.fromBlocks (cofactor z) 0 0 (0:Matrix Unit Unit K) := by
    ext (r|⟨⟩) (j|⟨⟩) <;> simp [cofactor,Matrix.submatrix,e,sideIndex,grad_extend_zero z zero,pad]
  have h := Matrix.rank_submatrix (cofactor (extend z)) e e
  rw [eq,sum_rank,Matrix.rank_zero,add_zero] at h
  exact h.symm

theorem hessian_rank_extend (z w : CellOf I → K)
    (image : (hessian (per K I) z) *ᵥ w=gradAt z) (null : gradAt z ⬝ᵥ w=0) :
    (hessian (per K (Option I)) (extend z)).rank=
      (hessian (per K I) z).rank+2*(cofactor z).rank := by
  let e := borderIndex I
  let C := cofactor z
  let H := hessian (per K I) z
  have eq : (hessBlock z).submatrix e e=Matrix.fromBlocks (arrow H (gradAt z)) 0 0
      (Matrix.fromBlocks (0:Matrix I I K) C Cᵀ 0) := by
    ext ((⟨r,i⟩|⟨⟩)|(r|i)) ((⟨s,j⟩|⟨⟩)|(s|j)) <;> rfl
  rw [hessian_extend,←Matrix.rank_submatrix (hessBlock z) e e,eq,sum_rank,cross_rank,
    arrow_rank H (gradAt z) w (hessian_grid_symmetry z).sym image null]

theorem pad_preserves_witness (z w : CellOf I → K) (zero : value z=0)
    (image : hessian (per K I) z *ᵥ w=gradAt z) (null : gradAt z ⬝ᵥ w=0) :
    hessian (per K (Option I)) (extend z) *ᵥ pad w=gradAt (extend z) ∧
      gradAt (extend z) ⬝ᵥ pad w=0 := by
  rw [grad_extend_zero z zero,hessian_extend]
  constructor
  · funext ⟨r,i⟩
    cases r with
    | none =>
      cases i with
      | none => simpa [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fintype.sum_option,hessBlock,pad]
          using null
      | some i => simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fintype.sum_option,hessBlock,pad]
    | some r =>
      cases i with
      | none => simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fintype.sum_option,hessBlock,pad]
      | some i => simpa [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fintype.sum_option,hessBlock,pad]
          using congrFun image (r,i)
  · simpa [dotProduct,Fintype.sum_prod_type,Fintype.sum_option,pad] using null

#print axioms cofactor_rank_extend
#print axioms hessian_rank_extend
#print axioms pad_preserves_witness
end PermanentBorder
