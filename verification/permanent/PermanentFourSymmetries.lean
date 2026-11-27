import PermanentFourEntries
/-! Row and column relabellings, transposition, and nonzero diagonal
rescalings preserve the Hessian-rank obstruction and transport its
row-supported and column-supported radical vectors. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
variable {K : Type*} [Field K]
def RowRel (z : Cell4 → K) (w : F → K) : Prop :=
  ∀ e : Cell4, ∑ j : F, H z e (3,j)*w j=0
def ColRel (z : Cell4 → K) (w : F → K) : Prop :=
  ∀ e : Cell4, ∑ i : F, H z e (i,3)*w i=0

theorem renamed_entries (p : Perm Cell4) (hp : rename p (per K F)=per K F)
    (z : Cell4 → K) (e f : Cell4) : H (z ∘ p) e f=H z (p e) (p f) := by
  have h := pderiv_rename p.injective f (per K F)
  rw [hp] at h
  rw [←hess_eq,←hess_eq]
  simp only [hessian,Matrix.of_apply,h,pderiv_rename p.injective,eval_rename]
theorem renamed_grad (p : Perm Cell4) (hp : rename p (per K F)=per K F)
    (z : Cell4 → K) (e : Cell4) : grad (z ∘ p) e=grad z (p e) := by
  have h := pderiv_rename p.injective e (per K F)
  rw [hp] at h
  rw [←grad_eq,←grad_eq,←grad_formula,←grad_formula,h,eval_rename]
theorem renamed_value (p : Perm Cell4) (hp : rename p (per K F)=per K F)
    (z : Cell4 → K) : PermanentBorder.value (z ∘ p)=PermanentBorder.value z := by
  change eval (z ∘ p) (per K F)=eval z (per K F)
  rw [←eval_rename,hp]
theorem renamed_rank (p : Perm Cell4) (hp : rename p (per K F)=per K F)
    (z : Cell4 → K) : (H (z ∘ p)).rank=(H z).rank := by
  have e : H (z ∘ p)=(H z).submatrix p p := Matrix.ext (renamed_entries p hp z)
  rw [e,Matrix.rank_submatrix]
def transposePoint (z : Cell4 → K) := z ∘ (Equiv.prodComm F F)
theorem col_to_row (z : Cell4 → K) (w : F → K) (rel : ColRel z w) :
    RowRel (transposePoint z) w := by
  intro e
  simp only [transposePoint,renamed_entries _ transpose_rename]
  exact rel (e.2,e.1)
theorem row_to_col (z : Cell4 → K) (w : F → K) (rel : RowRel z w) :
    ColRel (transposePoint z) w := by
  intro e
  simp only [transposePoint,renamed_entries _ transpose_rename]
  exact rel (e.2,e.1)

theorem row_reindex (z : Cell4 → K) (w : F → K) (rel : RowRel z w)
    (r c : Perm F) (hr : r 3=3) : RowRel (z ∘ r.prodCongr c) (w ∘ c) := by
  intro e
  calc _ = ∑ j : F, H z ((r.prodCongr c) e) ((r.prodCongr c) (3,j))*w (c j) := by
         apply Finset.sum_congr rfl
         intro t _
         rw [renamed_entries (r.prodCongr c) (row_column_rename r c)]
         rfl
       _ = 0 := by
         rcases e with ⟨x,y⟩
         simpa [Equiv.prodCongr_apply,hr] using
           (Equiv.sum_comp c (fun j ↦ H z (r x,c y) (3,j)*w j)).trans (rel _)
theorem col_reindex (z : Cell4 → K) (w : F → K) (rel : ColRel z w)
    (r c : Perm F) (hc : c 3=3) : ColRel (z ∘ r.prodCongr c) (w ∘ r) := by
  intro e
  calc _ = ∑ i : F, H z ((r.prodCongr c) e) ((r.prodCongr c) (i,3))*w (r i) := by
         apply Finset.sum_congr rfl
         intro t _
         rw [renamed_entries (r.prodCongr c) (row_column_rename r c)]
         rfl
       _ = 0 := by
         rcases e with ⟨x,y⟩
         simpa [Equiv.prodCongr_apply,hc] using
           (Equiv.sum_comp r (fun i ↦ H z (r x,c y) (i,3)*w i)).trans (rel _)

def scale (a b : F → K) (z : Cell4 → K) (e : Cell4) := a e.1*b e.2*z e
def factor (a b : F → K) := (∏ j, a j)*(∏ j, b j)
private theorem complement_product (a : F → K) (r s : F) (h : r≠s) :
    a r*a s*a (otherTwo r s).1*a (otherTwo r s).2=∏ j, a j := by
  fin_cases r <;> fin_cases s <;> simp [otherTwo,Fin.prod_univ_succ] at * <;> ring

theorem scaled_entries (a b : F → K) (z : Cell4 → K) (e f : Cell4) :
  (a e.1*b e.2)*(a f.1*b f.2)*H (scale a b z) e f=factor a b*H z e f := by
  by_cases h : e.1=f.1 ∨ e.2=f.2
  · simp [H,h]
  · have rn : e.1≠f.1 := fun q ↦ h (Or.inl q)
    have cn : e.2≠f.2 := fun q ↦ h (Or.inr q)
    simp only [H,Matrix.of_apply,ite_eq_right h,two,scale,factor]
    rw [←complement_product a _ _ rn,←complement_product b _ _ cn]
    ring

theorem scale_rank_le (a b : F → K) (ha : ∀ j, a j≠0) (hb : ∀ j, b j≠0)
    (z : Cell4 → K) : (H (scale a b z)).rank≤(H z).rank := by
  let L := Matrix.diagonal (fun e : Cell4 ↦ factor a b/(a e.1*b e.2))
  let R := Matrix.diagonal (fun e : Cell4 ↦ (a e.1*b e.2)⁻¹)
  have h : H (scale a b z)=L*H z*R := by
    ext e f
    simp only [L,R,Matrix.mul_diagonal,Matrix.diagonal_mul]
    field_simp [ha,hb]
    linear_combination scaled_entries a b z e f
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem scale_corner (a b : F → K) (z : Cell4 → K) :
    grad (scale a b z) (3,3) =
    (a 0*a 1*a 2*b 0*b 1*b 2)*grad z (3,3) := by
  simp [grad,otherThree,three,scale]
  ring

theorem scale_value (a b : F → K) (z : Cell4 → K) :
    PermanentBorder.value (scale a b z)=factor a b*PermanentBorder.value z := by
  have h := congrArg (eval z) (row_column_twist a b)
  change eval (fun i ↦ a i.1*b i.2*z i) (per K F)=factor a b*eval z (per K F)
  simpa [eval_twist,factor] using h

theorem row_scale (z : Cell4 → K) (w : F → K) (rel : RowRel z w)
    (a b : F → K) (ha : ∀ j, a j≠0) (hb : ∀ j, b j≠0) :
    RowRel (scale a b z) (fun j ↦ b j*w j) := by
  intro e
  apply (mul_eq_zero.mp (show (a e.1*b e.2*a 3)*(∑ j : F, H (scale a b z) e (3,j)*(b j*w j))=0 from ?_)).resolve_left
    (mul_ne_zero (mul_ne_zero (ha _) (hb _)) (ha _))
  calc _=∑ j : F, factor a b*(H z e (3,j)*w j) := by
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro j _
         linear_combination w j * scaled_entries a b z e (3,j)
       _=0 := by rw [←Finset.mul_sum,rel,mul_zero]

theorem col_scale (z : Cell4 → K) (w : F → K) (rel : ColRel z w)
    (a b : F → K) (ha : ∀ j, a j≠0) (hb : ∀ j, b j≠0) :
    ColRel (scale a b z) (fun i ↦ a i*w i) := by
  intro e
  apply (mul_eq_zero.mp (show (a e.1*b e.2*b 3)*(∑ i : F, H (scale a b z) e (i,3)*(a i*w i))=0 from ?_)).resolve_left
    (mul_ne_zero (mul_ne_zero (ha _) (hb _)) (hb _))
  calc _=∑ i : F, factor a b*(H z e (i,3)*w i) := by
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro i _
         linear_combination w i * scaled_entries a b z e (i,3)
       _=0 := by rw [←Finset.mul_sum,rel,mul_zero]

#print axioms scale_rank_le
end PermanentOrderFour
