import PermanentFourSymmetries
import AlternatingMatrixRank
/-! A small Hessian has nonzero radical directions supported on its last
row and column. At a smooth corner both have zero corner coordinate. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
variable {K : Type*} [Field K]
theorem H_symmetric (z : Cell4 → K) : (H z).IsSymm := by
  rw [←hess_eq]
  ext e f
  change eval z (pderiv f (pderiv e _))=eval z (pderiv e (pderiv f _))
  rw [pderiv_comm]

theorem small_relations (z : Cell4 → K) (small : (H z).rank≤7) :
    (∃ w : F → K, w≠0 ∧ RowRel z w) ∧ (∃ v : F → K, v≠0 ∧ ColRel z v) := by
  have bound : (H z).rank<2*Fintype.card F := by change _<8; omega
  constructor
  · obtain ⟨w,hn,eq⟩ := isotropic_columns_kernel (H z) (H_symmetric z) (fun j : F ↦ (3,j))
      (by intro i j; simp [H]) bound
    exact ⟨w,hn,fun e ↦ congrFun eq e⟩
  · obtain ⟨w,hn,eq⟩ := isotropic_columns_kernel (H z) (H_symmetric z) (fun i : F ↦ (i,3))
      (by intro i j; simp [H]) bound
    exact ⟨w,hn,fun e ↦ congrFun eq e⟩

theorem row_rel_corner (z : Cell4 → K) (w : F → K) (rel : RowRel z w)
    (p : grad z (3,3)≠0) : w 3=0 := by
  have h0 := rel (0,0)
  have h1 := rel (0,1)
  have h2 := rel (0,2)
  have h3 := rel (1,3)
  have h4 := rel (2,3)
  apply (mul_eq_zero.mp (show grad z (3,3)*w 3=0 from ?_)).resolve_left p
  simp [-mul_eq_zero,H,grad,three,two,otherTwo,otherThree,Fin.sum_univ_succ] at h0 h1 h2 h3 h4 ⊢
  linear_combination z (0,0)*h0+z (0,1)*h1+z (0,2)*h2-z (1,3)*h3-z (2,3)*h4

theorem col_rel_corner (z : Cell4 → K) (w : F → K) (rel : ColRel z w)
    (p : grad z (3,3)≠0) : w 3=0 := by
  apply row_rel_corner (transposePoint z) w (col_to_row z w rel)
  rw [transposePoint,renamed_grad _ transpose_rename]
  exact p

private theorem contains_last : ∀ r s : F, r≠s → r≠3 → s≠3 →
    (otherTwo r s).1=3 ∨ (otherTwo r s).2=3 := by decide +kernel

theorem zero_row_even (z : Cell4 → K) (zero : ∀ j, z (3,j)=0) : Even (H z).rank := by
  let D := Matrix.diagonal (fun e : Cell4 ↦ if e.1=3 then (1:K) else -1)
  have inv : IsUnit D.det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (by
      intro e _
      by_cases h : e.1=3 <;> simp [h]))
  have off (e f : Cell4) (he : e.1≠3) (hf : f.1≠3) : H z e f=0 := by
    by_cases h : e.1=f.1 ∨ e.2=f.2
    · simp [H,h]
    · rcases contains_last e.1 f.1 (fun q ↦ h (Or.inl q)) he hf with t|t <;> simp [H,h,t,two,zero]
  have hz (e f : Cell4) (he : e.1=3) (hf : f.1=3) : H z e f=0 := by simp [H,he,hf]
  have sym (e f : Cell4) : H z f e=H z e f := (H_symmetric z).apply e f
  have h := AlternatingMatrix.even_rank (D*H z) (by
    intro e f
    by_cases he : e.1=3 <;> by_cases hf : f.1=3
    · simp [D,Matrix.diagonal_mul,he,hf,hz e f he hf,hz f e hf he]
    · simp [D,Matrix.diagonal_mul,he,hf,sym e f]
    · simp [D,Matrix.diagonal_mul,he,hf,sym e f]
    · simp [D,Matrix.diagonal_mul,he,hf,off e f he hf,off f e hf he]) (by
      intro e
      simp [D,Matrix.diagonal_mul,H])
  rwa [Matrix.rank_mul_eq_right_of_isUnit_det D _ inv] at h

def leg (z : Cell4 → K) : Fin 3 → K := fun i ↦ z (3,i.castSucc)

theorem leg_nonzero (z : Cell4 → K) (flat : PermanentBorder.value z=0)
    (smooth : grad z (3,3)≠0) (odd : ¬Even (H z).rank) : leg z≠0 := by
  intro empty
  have h (j : Fin 3) : z (3,j.castSucc)=0 := congrFun empty j
  have h0 : z (3,0)=0 := h 0
  have h1 : z (3,1)=0 := h 1
  have h2 : z (3,2)=0 := h 2
  rw [value_eq] at flat
  simp [Fin.sum_univ_succ,h0,h1,h2] at flat
  have h3 := flat.resolve_right smooth
  apply odd (zero_row_even z (fun j ↦ ?_))
  fin_cases j <;> assumption

#print axioms small_relations
#print axioms zero_row_even
end PermanentOrderFour
