import PermanentWeightedWords
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow.Weighted
variable {R I J : Type*} [CommRing R] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
theorem poly_congr (b : I ≃ J) : rename (b.prodCongr b) (per R I)=per R J := by
  simp only [per,Matrix.permanent,map_sum,map_prod,PermanentCuts.generic,Matrix.of_apply,rename_X]
  apply Fintype.sum_equiv (Equiv.permCongr b)
  intro p
  apply Fintype.prod_equiv b
  intro j
  simp [Equiv.permCongr_apply]

theorem board_reindex (b : I ≃ J) (c : I) (s : J→R) :
    board c (s ∘ b) ∘ (b.prodCongr b).symm=board (b c) s := by
  have t : total c (s ∘ b)=total (b c) s := by
    apply Fintype.sum_equiv b
    intro i
    simp
  funext ⟨i,j⟩
  obtain ⟨a,rfl⟩ := b.surjective i
  obtain ⟨d,rfl⟩ := b.surjective j
  simp [board,t]

theorem law_reindex (b : I ≃ J) (c i j : I) (s : J→R) (v : CellOf I)
    (h : Law c i j (s ∘ b) v) : Law (b c) (b i) (b j) s (b.prodCongr b v) := by
  obtain ⟨hc,hf,hr⟩ := h
  let u := b.prodCongr b
  have undo : (board c (s ∘ b) ∘ u.symm) ∘ u=board c (s ∘ b) :=
    funext fun e ↦ congrArg _ (u.symm_apply_apply e)
  have g (a d : I) : gradAt (board (b c) s) (b a,b d)=gradAt (board c (s ∘ b)) (a,d) := by
    change gradAt (board (b c) s) (u (a,d))=_
    rw [←grad_formula,←board_reindex,←poly_congr b,pderiv_rename u.injective,eval_rename,undo,grad_formula]
  have sec (a d : I) :
      hessian (per R J) (board (b c) s) (b a,b d) (b.prodCongr b v)=hessian (per R I) (board c (s ∘ b)) (a,d) v := by
    change eval (board (b c) s) (pderiv (u (a,d)) (pderiv (u v) (per R J)))=_
    rw [←board_reindex,←poly_congr b,pderiv_rename u.injective,pderiv_rename u.injective,eval_rename,undo]
    rfl
  have sk (a : I) : skip c a (s ∘ b)=skip (b c) (b a) s := by
    apply Fintype.prod_equiv b
    intro i
    simp
  refine ⟨?_,?_,?_⟩
  · rw [g,hc]
    apply Fintype.prod_equiv b
    intro i
    simp
  · simpa only [firstJet,g] using hf
  · change _=(if u v=u (j,i) then _ else _)
    simp only [rowJet,sec,u.apply_eq_iff_eq]
    unfold rowJet at hr
    simpa only [sk] using hr

end PermanentArrow.Weighted
