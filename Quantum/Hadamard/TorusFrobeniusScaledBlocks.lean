import Quantum.Hadamard.TorusFrobeniusPaley

/-! The Paley conference construction with an arbitrary even-order modular
Hadamard matrix in its nonzero positions and a signed row permutation on its diagonal. -/
noncomputable section
namespace HadamardMod.TorusFrobenius
open Finset

private def dot {m:ℕ} {I:Type} [Fintype I] (u v:I→ZMod m) := ∑j,u j*v j

private theorem dot_scale {m:ℕ} {I:Type} [Fintype I] (a b:ZMod m) (u v:I→ZMod m) :
    (∑j,(a*u j)*(b*v j))=a*b*dot u v := by
  rw [dot,Finset.mul_sum]
  exact sum_congr rfl (fun _ _ => by ring)

private def rotate {m:ℕ} {U:Type} (A:RowMatrix m (U⊕U)) : RowMatrix m (U⊕U)
  | .inl i,j => A (.inr i) j
  | .inr i,j => -A (.inl i) j

private theorem rotated {m:ℕ} {U:Type} [Fintype U] (A:RowMatrix m (U⊕U)) (g:Good A) :
    Good (rotate A) ∧ ∀ i j,dot (A i) (rotate A j)+dot (rotate A i) (A j)=0 := by
  classical
  have gram (i j:U⊕U) : dot (A i) (A j)=if i=j then (Fintype.card (U⊕U):ZMod m) else 0 := by
    by_cases h:i=j
    · subst j; simpa [dot] using g.norm_rows i
    · simpa [dot,h] using g.ortho i j h
  have negRight (i j:U⊕U) : dot (A i) (fun k => -A j k) = -dot (A i) (A j) := by
    simp [dot,Finset.sum_neg_distrib]
  have negLeft (i j:U⊕U) : dot (fun k => -A i k) (A j) = -dot (A i) (A j) := by
    simp [dot,Finset.sum_neg_distrib]
  constructor
  · constructor
    · rintro (i|i) j
      · exact g.sign _ _
      · rcases g.sign (.inl i) j with h|h <;> simp [rotate,h,Sign]
    · rintro (i|i) (j|j) ne
      · exact g.ortho _ _ (fun h => ne (congrArg Sum.inl (Sum.inr.inj h)))
      · simp only [rotate,mul_neg,Finset.sum_neg_distrib,g.ortho _ _ (by simp : Sum.inr i ≠ (Sum.inl j:U⊕U)),neg_zero]
      · simp only [rotate,neg_mul,Finset.sum_neg_distrib,g.ortho _ _ (by simp : Sum.inl i ≠ (Sum.inr j:U⊕U)),neg_zero]
      · simpa only [rotate,neg_mul_neg] using g.ortho (Sum.inl i) (Sum.inl j)
          (fun h => ne (congrArg Sum.inr (Sum.inl.inj h)))
  · rintro (i|i) (j|j)
    · change dot (A (.inl i)) (A (.inr j))+dot (A (.inr i)) (A (.inl j))=0
      simp [gram]
    · change dot (A (.inl i)) (fun k => -A (.inl j) k)+dot (A (.inr i)) (A (.inr j))=0
      simp [negRight,gram]
    · change dot (A (.inr i)) (A (.inr j))+dot (fun k => -A (.inl i) k) (A (.inl j))=0
      simp [negLeft,gram]
    · change dot (A (.inr i)) (fun k => -A (.inl j) k)+dot (fun k => -A (.inl i) k) (A (.inr j))=0
      simp [negRight,negLeft,gram]

def reduce {m:ℕ} {O:Type} [Fintype O] (C:Conference 0 O) : Conference m O := by
  let z : O→O→ℤ := C.entry
  refine ⟨fun i j => (z i j:ZMod m),?_,?_,?_⟩
  · intro i
    have h : z i i=0 := C.diag i
    simp only [h,Int.cast_zero]
  · intro i j ne
    rcases (show z i j=1 ∨ z i j= -1 from C.sign i j ne) with h|h <;> simp [h,Sign]
  · intro i j ne
    have h : (∑ k,z i k*z j k)=0 := C.off i j ne
    simpa only [Int.cast_sum,Int.cast_mul,Int.cast_zero] using congrArg (fun x:ℤ => (x:ZMod m)) h

theorem conference_scaled {m:ℕ} {O U:Type} [Fintype O] [DecidableEq O] [Fintype U]
    (C:Conference m O) (sym:∀i j,C.entry i j=C.entry j i)
    (e:O≃O) (inv:∀i j,C.entry (e i) (e j)=C.entry i j)
    (A:RowMatrix m (U⊕U)) (g:Good A) :
    ∃ H:RowMatrix m (O×(U⊕U)), Good H ∧
      ∀ x y,H (e x.1,x.2) (e y.1,y.2)=H x y := by
  classical
  let B := rotate A
  obtain ⟨gb,skew⟩ := rotated A g
  let H (i j:O×(U⊕U)) := if i.1=j.1 then B i.2 j.2 else C.entry i.1 j.1*A i.2 j.2
  refine ⟨H,⟨?_,?_⟩,?_⟩
  · rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases h:i=j
    · simpa [H,h] using gb.sign x y
    · simpa [H,h] using sign_mul (C.sign i j h) (g.sign x y)
  · rintro ⟨i,x⟩ ⟨k,y⟩ ne
    rw [Fintype.sum_prod_type]
    by_cases ik:i=k
    · subst k
      have xy:x≠y := fun h => ne (Prod.ext rfl h)
      apply sum_eq_zero
      intro j _
      by_cases ij:i=j
      · simpa [H,ij] using gb.ortho x y xy
      · simp only [H,ij,ite_false,dot_scale,dot,g.ortho _ _ xy,mul_zero]
    · have fibre (j:O) : (∑z,H (i,x) (j,z)*H (k,y) (j,z)) =
          C.entry i j*C.entry k j*dot (A x) (A y)+
          (if i=j then C.entry k i*dot (B x) (A y) else 0)+
          (if k=j then C.entry i k*dot (A x) (B y) else 0) := by
        by_cases ij:i=j
        · subst j
          simp only [H,ite_true,if_pos rfl,if_neg (Ne.symm ik),C.diag,zero_mul,zero_add,add_zero,dot]
          rw [mul_sum]
          exact sum_congr rfl (fun _ _ => by ring)
        by_cases kj:k=j
        · subst j
          simp only [H,ite_true,if_pos rfl,if_neg ik,C.diag,mul_zero,zero_mul,zero_add,add_zero,dot]
          rw [mul_sum]
          exact sum_congr rfl (fun _ _ => by ring)
        · simp only [H,ij,kj,ite_false,add_zero,dot_scale]
      simp only [fibre,sum_add_distrib,←sum_mul,C.off _ _ ik,zero_mul,sum_ite_eq,mem_univ,
        ite_true,zero_add,sym k i]
      rw [←mul_add,add_comm (dot (B x) (A y)),skew x y,mul_zero]
  · rintro ⟨i,x⟩ ⟨j,y⟩
    simp only [H,e.injective.eq_iff,inv]

end HadamardMod.TorusFrobenius


