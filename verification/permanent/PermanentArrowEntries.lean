import PermanentArrowSmall1
import PermanentArrowSmall2
import PermanentArrowSmall3
import PermanentArrowSmall4
import PermanentArrowSmall5
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow
variable {K I J : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def States (K : Type*) [Field K] (c : I) (e f : CellOf I) : Prop :=
  PermanentBorder.value (point K c)=0 ∧ gradAt (point K c) (c,c)=1 ∧
    hessian (per K I) (point K c) e f=(entry c e f:K)

theorem states_equiv (b : I ≃ J) (c : I) (e f : CellOf I) (h : States K c e f) :
    States K (b c) (b.prodCongr b e) (b.prodCongr b f) := by
  obtain ⟨v,g,r⟩ := h
  refine ⟨?_,?_,?_⟩
  · rw [←point_equiv b c,transport_value,v]
  · change gradAt (point K (b c)) (b.prodCongr b (c,c))=1
    rw [←point_equiv b c,transport_gradient,g]
  · let u := b.prodCongr b
    change eval (point K (b c)) (pderiv (u e) (pderiv (u f) (per K J)))=_
    rw [←point_equiv b c,←rename_permanent b,pderiv_rename u.injective,pderiv_rename u.injective,
      eval_rename,entry_equiv]
    have unmap : (point K c ∘ u.symm) ∘ u=point K c := funext fun i ↦ congrArg _ (u.symm_apply_apply i)
    change eval ((point K c ∘ u.symm) ∘ u) _=_
    rw [unmap]
    exact r

theorem leaf_states (c : I) (e f : CellOf I) (h : States K c e f) : States K (some c) (old e) (old f) := by
  obtain ⟨v,g,r⟩ := h
  refine ⟨?_,?_,?_⟩
  · rw [←leaf_point]
    change eval (leaf c (point K c)) (per K (Option I))=0
    rw [←eval_spec,spec_per]
    exact v
  · change gradAt (point K (some c)) (old (c,c))=1
    rw [←leaf_point,leaf_gradient,g]
  · rw [←leaf_point,leaf_hessian,leaf_entry,r]

private theorem finite_base {n : ℕ} [NeZero n] (e f : CellOf (Fin n))
    (v : integralValue (point ℤ (0:Fin n))=0) (g : gradAt (point ℤ (0:Fin n)) (0,0)=1)
    (r : ∀ e f, secondAt (point ℤ (0:Fin n)) e f=entry (0:Fin n) e f) : States K (0:Fin n) e f := by
  refine ⟨?_,?_,?_⟩
  · rw [point_cast,cast_value,v,Int.cast_zero]
  · rw [point_cast,castPoint,grad_map,g,map_one]
  · rw [second_formula,point_cast,castPoint,second_map,r]
    rfl

private theorem closed_1 (e f : CellOf (Fin 1)) : States K (0:Fin 1) e f :=
  finite_base e f (by decide +kernel) (by decide +kernel) small_1

private theorem closed_2 (e f : CellOf (Fin 2)) : States K (0:Fin 2) e f :=
  finite_base e f (by decide +kernel) (by decide +kernel) small_2

private theorem closed_3 (e f : CellOf (Fin 3)) : States K (0:Fin 3) e f :=
  finite_base e f (by decide +kernel) (by decide +kernel) small_3

private theorem closed_4 (e f : CellOf (Fin 4)) : States K (0:Fin 4) e f :=
  finite_base e f (by decide +kernel) (by decide +kernel) small_4

private theorem closed_5 (e f : CellOf (Fin 5)) : States K (0:Fin 5) e f :=
  finite_base e f (by decide +kernel) (by decide +kernel) small_5

private theorem small {n : ℕ} [NeZero n] (hn : n≤5) (e f : CellOf (Fin n)) : States K (0:Fin n) e f := by
  have pos := NeZero.pos n
  interval_cases n
  · exact closed_1 e f
  · exact closed_2 e f
  · exact closed_3 e f
  · exact closed_4 e f
  · exact closed_5 e f

private theorem unused_index (c : I) (e f : CellOf I) (large : 5<Fintype.card I) :
    ∃ t : I, c≠t ∧ e.1≠t ∧ e.2≠t ∧ f.1≠t ∧ f.2≠t := by
  let s : Finset I := {c,e.1,e.2,f.1,f.2}
  have cap : s.card≤5 := by
    dsimp [s]
    calc
      _ ≤ _ := Finset.card_insert_le _ _
      _ ≤ _ := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1) 1
      _ = 5 := by simp
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show s.card<(univ:Finset I).card from cap.trans_lt large)
  simp only [s,Finset.mem_insert,Finset.mem_singleton] at ht
  exact ⟨t,by tauto,by tauto,by tauto,by tauto,by tauto⟩

theorem all_entries (K : Type*) [Field K] {I : Type*} [Fintype I] [DecidableEq I]
    (c : I) (e f : CellOf I) : States K c e f := by
  let n := Fintype.card I
  suffices h : ∀ (m : ℕ) (J : Type _) [Fintype J] [DecidableEq J], Fintype.card J=m →
      ∀ (c : J) (e f : CellOf J), States K c e f by
    exact h n I rfl c e f
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro J _ _ card c e f
    by_cases hm : m≤5
    · have positive : 0<m := card ▸ Fintype.card_pos_iff.mpr ⟨c⟩
      let _ : NeZero m := ⟨by omega⟩
      let b := Fintype.equivFinOfCardEq card
      let v := b.trans (Equiv.swap (b c) 0)
      have vc : v c=0 := by simp [v]
      have base : States K (v c) (v.prodCongr v e) (v.prodCongr v f) := by
        rw [vc]
        exact small hm _ _
      change States K c e f
      have back := states_equiv v.symm (v c) _ _ base
      change States K (v.symm (v c)) ((v.prodCongr v).symm (v.prodCongr v e)) ((v.prodCongr v).symm (v.prodCongr v f)) at back
      simpa only [Equiv.symm_apply_apply] using back
    · obtain ⟨t,ct,a,b,d,k⟩ := unused_index c e f (by omega)
      let S := {x : J // x≠t}
      let u := Equiv.optionSubtypeNe t
      let c' : S := ⟨c,ct⟩
      let e' : CellOf S := (⟨e.1,a⟩,⟨e.2,b⟩)
      let f' : CellOf S := (⟨f.1,d⟩,⟨f.2,k⟩)
      have less : Fintype.card S<m := by
        rw [←card]
        exact Fintype.card_subtype_lt (x:=t) (by simp)
      have taken := leaf_states c' e' f' (ih _ less S rfl c' e' f')
      simpa [u,c',e',f',old] using states_equiv u (some c') (old e') (old f') taken

#print axioms all_entries
end PermanentArrow
