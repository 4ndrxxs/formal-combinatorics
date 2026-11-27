import PermanentFourRadical

/-! The row and column symmetries independently move the supports of
two radical vectors to initial segments and normalize their coefficients. -/
noncomputable section
open Matrix Equiv Finset PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
variable {K : Type*} [Field K]
def shape (K : Type*) [Field K] (k : Fin 3) (j : F) : K :=
  if j.val≤k.val then (if j=1 then -1 else 1) else 0
private theorem support_patterns : ∀ u : F → Bool, u 3=false → (∃ i, u i=true) →
    ∃ k : Fin 3, ∃ r : Perm F, r 3=3 ∧ ∀ i, u (r i)=decide (i.val≤k.val) := by decide +kernel

theorem normalize_vector (w : F → K) (nz : w≠0) (last : w 3=0) :
    ∃ k : Fin 3, ∃ r : Perm F, ∃ a : F → K,
    r 3=3 ∧ (∀ i, a i≠0) ∧ ∀ i, a i*w (r i)=shape K k i := by
  classical
  let u := fun i ↦ decide (w i≠0)
  obtain ⟨k,r,r3,hs⟩ := support_patterns u (by simp [u,last]) (by
    by_contra! all
    apply nz
    funext i
    simpa [u] using all i)
  let a := fun i ↦ if w (r i)=0 then 1 else (if i=1 then -1 else 1)/w (r i)
  refine ⟨k,r,a,r3,?_,?_⟩
  · intro i
    by_cases z : w (r i)=0
    · simp [a,z]
    · simp only [a,ite_eq_right z,ne_eq,div_eq_zero_iff,z,or_false]
      split <;> simp
  · intro i
    have hi : w (r i)≠0 ↔ i.val≤k.val := by
      have h := hs i
      by_cases hw : w (r i)=0 <;> by_cases hc : i.val≤k.val <;> simp [u,hw,hc] at h ⊢
    by_cases z : w (r i)=0
    · have h : ¬i.val≤k.val := fun t ↦ hi.mpr t z
      simp [a,z,shape,h]
    · simp [a,z,shape,hi.mp z]

def BottomNonzero (z : Cell4 → K) : Prop := ∃ i : F, i≠3 ∧ z (3,i)≠0
def SideNonzero (z : Cell4 → K) : Prop := ∃ i : F, i≠3 ∧ z (i,3)≠0
structure SmallChart (z : Cell4 → K) : Prop where
  small : (H z).rank≤7
  smooth : grad z (3,3)≠0
  flat : PermanentBorder.value z=0
  bottom : BottomNonzero z
  side : SideNonzero z

theorem SmallChart.transpose {z : Cell4 → K} (c : SmallChart z) : SmallChart (transposePoint z) := by
  refine ⟨?_,?_,?_,c.side,c.bottom⟩
  · rw [transposePoint,renamed_rank _ transpose_rename]
    exact c.small
  · rw [transposePoint,renamed_grad _ transpose_rename]
    exact c.smooth
  · rw [transposePoint,renamed_value _ transpose_rename]
    exact c.flat

theorem SmallChart.reindex {z : Cell4 → K} (h : SmallChart z) (r c : Perm F)
    (hr : r 3=3) (hc : c 3=3) : SmallChart (z ∘ r.prodCongr c) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [renamed_rank _ (row_column_rename r c)]
    exact h.small
  · rw [renamed_grad _ (row_column_rename r c)]
    simpa [Equiv.prodCongr_apply,hr,hc] using h.smooth
  · rw [renamed_value _ (row_column_rename r c)]
    exact h.flat
  · obtain ⟨i,hi,wi⟩ := h.bottom
    refine ⟨c.symm i,fun e ↦ hi (by simpa [hc] using congrArg c e),?_⟩
    simpa [Function.comp_apply,Equiv.prodCongr_apply,hr] using wi
  · obtain ⟨i,hi,wi⟩ := h.side
    refine ⟨r.symm i,fun e ↦ hi (by simpa [hr] using congrArg r e),?_⟩
    simpa [Function.comp_apply,Equiv.prodCongr_apply,hc] using wi

theorem SmallChart.scale {z : Cell4 → K} (h : SmallChart z) (a b : F → K)
    (ha : ∀ i, a i≠0) (hb : ∀ i, b i≠0) : SmallChart (PermanentOrderFour.scale a b z) := by
  refine ⟨(scale_rank_le a b ha hb z).trans h.small,?_,?_,?_,?_⟩
  · rw [scale_corner]
    exact mul_ne_zero (by simp [ha,hb]) h.smooth
  · rw [scale_value,h.flat,mul_zero]
  · obtain ⟨i,hi,wi⟩ := h.bottom
    exact ⟨i,hi,mul_ne_zero (mul_ne_zero (ha _) (hb _)) wi⟩
  · obtain ⟨i,hi,wi⟩ := h.side
    exact ⟨i,hi,mul_ne_zero (mul_ne_zero (ha _) (hb _)) wi⟩

theorem normalized_chart {z : Cell4 → K} (h : SmallChart z) :
    ∃ y : Cell4 → K, ∃ i j : Fin 3, SmallChart y ∧ ColRel y (shape K i) ∧ RowRel y (shape K j) := by
  obtain ⟨⟨v,nv,row⟩,⟨w,nw,col⟩⟩ := small_relations z h.small
  obtain ⟨i,r,a,hr,ha,ar⟩ := normalize_vector w nw (col_rel_corner z w col h.smooth)
  obtain ⟨j,c,b,hc,hb,bc⟩ := normalize_vector v nv (row_rel_corner z v row h.smooth)
  let x := z ∘ r.prodCongr c
  refine ⟨scale a b x,i,j,(h.reindex r c hr hc).scale a b ha hb,?_,?_⟩
  · have e := col_scale x (w ∘ r) (col_reindex z w col r c hc) a b ha hb
    have t : (fun k ↦ a k*(w ∘ r) k)=shape K i := funext ar
    rwa [t] at e
  · have e := row_scale x (v ∘ c) (row_reindex z v row r c hr) a b ha hb
    have t : (fun k ↦ b k*(v ∘ c) k)=shape K j := funext bc
    rwa [t] at e

theorem chart_of_seven (z : Cell4 → K) (flat : PermanentBorder.value z=0)
    (smooth : cofactor z≠0) (rank : (hessian (per K F) z).rank=7) : ∃ x : Cell4 → K, SmallChart x := by
  obtain ⟨i,j,h⟩ : ∃ i j : F, grad z (i,j)≠0 := by
    by_contra! empty
    apply smooth
    ext i j
    exact (grad_eq z (i,j)).trans (empty i j)
  let r := Equiv.swap 3 i
  let c := Equiv.swap 3 j
  let x := z ∘ r.prodCongr c
  have hx : grad x (3,3)≠0 := by
    change grad (z ∘ r.prodCongr c) (3,3)≠0
    rw [renamed_grad _ (row_column_rename r c)]
    simpa [r,c] using h
  have zx : PermanentBorder.value x=0 := (renamed_value _ (row_column_rename r c) z).trans flat
  have rk : (H x).rank=7 := by
    change (H (z ∘ r.prodCongr c)).rank=7
    rw [renamed_rank _ (row_column_rename r c),←hess_eq,rank]
  have nonzero (y : Cell4 → K) (p : grad y (3,3)≠0) (zy : PermanentBorder.value y=0)
      (ry : (H y).rank=7) : BottomNonzero y := by
    have legnz := leg_nonzero y zy p (by rw [ry]; decide)
    unfold BottomNonzero
    by_contra! missing
    apply legnz
    funext t
    apply missing t.castSucc
    exact Fin.ne_of_lt (Fin.castSucc_lt_last t)
  refine ⟨x,⟨rk.le,hx,zx,nonzero x hx zx rk,?_⟩⟩
  apply nonzero (transposePoint x)
  · rw [transposePoint,renamed_grad _ transpose_rename]
    exact hx
  · rw [transposePoint,renamed_value _ transpose_rename,zx]
  · rw [transposePoint,renamed_rank _ transpose_rename,rk]

#print axioms normalized_chart
#print axioms chart_of_seven
end PermanentOrderFour
