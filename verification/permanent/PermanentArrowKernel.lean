import PermanentArrowReduction

/-! The radical consists of the lifted trace-zero diagonals. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem off_coordinate (w : Bigger I → K) (i j : I) (ij : i≠j) :
    (model K I *ᵥ w) (old (i,j))-(model K I *ᵥ w) (left i)-(model K I *ᵥ w) (right j)+
      (model K I *ᵥ w) corner= -4*w (old (j,i)) := by
  simp only [Matrix.mulVec,dotProduct,←Finset.sum_sub_distrib,←Finset.sum_add_distrib,
    ←sub_mul,←add_mul]
  simp [off_rows i j ij,ite_mul]

private theorem strip_action (w : Bigger I → K) (inside : ∀ i j, w (old (i,j))=0) :
    (model K I *ᵥ w) corner=0 ∧
    (∀ i, (model K I *ᵥ w) (left i)=w (right i)) ∧
    (∀ i, (model K I *ᵥ w) (right i)=w (left i)) := by
  have vanish (i j : I) : w (some i,some j)=0 := inside i j
  refine ⟨?_,fun i ↦ ?_,fun i ↦ ?_⟩ <;>
    simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fintype.sum_option,
      model,entry,other,corner,left,right,vanish,ite_mul]

private theorem corner_image (w : Bigger I → K) (inside : ∀ i j,w (old (i,j))=0)
    (sl : ∀ i,w (left i)=0) (sr : ∀ i,w (right i)=0) (i : I) :
    (model K I *ᵥ w) (old (i,i))=w corner := by
  have va (a b : I) : w (some a,some b)=0 := inside a b
  have vb (a : I) : w (some a,none)=0 := sl a
  have vc (a : I) : w (none,some a)=0 := sr a
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fintype.sum_option,model,entry,other,old,corner,va,vb,vc]

theorem ker_iff [Nonempty I] (two_ne : (2:K)≠0) (w : Bigger I → K) :
    model K I *ᵥ w=0 ↔
      (∑ i, w (old (i,i)))=0 ∧ w=diagonalLift (fun i ↦ w (old (i,i))) := by
  constructor
  · intro hw
    let d (i : I) := w (old (i,i))
    let v := w-diagonalLift d
    have va (i j : I) : v (old (i,j))=0 := by
      by_cases h : i=j
      · subst j; simp [v,d,diagonalLift,old]
      · have a := off_coordinate w j i (Ne.symm h)
        rw [hw] at a
        have four : (4:K)≠0 := by
          have p := mul_ne_zero two_ne two_ne
          convert p using 1
          norm_num
        have z : w (old (i,j))=0 := by simpa [four] using a.symm
        simp [v,diagonalLift,old,h] at z ⊢
        exact z
    obtain ⟨vc,vl,vr⟩ := strip_action v va
    have act : model K I *ᵥ v= -(∑ i,d i) • common K := by
      simp [v,Matrix.mulVec_sub,hw,image_lift]
    have trace : (∑ i,d i)=0 := by
      rw [act] at vc
      simpa [corner,common] using vc
    have vz : model K I *ᵥ v=0 := by rw [act,trace,neg_zero,zero_smul]
    have sl (i : I) : v (left i)=0 := by simpa [vz] using (vr i).symm
    have sr (i : I) : v (right i)=0 := by simpa [vz] using (vl i).symm
    have sc : v corner=0 := by
      obtain ⟨i⟩ := ‹Nonempty I›
      simpa [vz] using (corner_image v va sl sr i).symm
    refine ⟨trace,sub_eq_zero.mp (show v=0 from ?_)⟩
    funext ⟨a,b⟩
    cases a with
    | none => cases b with
      | none => exact sc
      | some b => exact sr b
    | some a => cases b with
      | none => exact sl a
      | some b => exact va a b
  · rintro ⟨trace,e⟩
    conv_lhs => rw [e]
    rw [image_lift,trace,zero_smul]

#print axioms ker_iff
end PermanentArrow
