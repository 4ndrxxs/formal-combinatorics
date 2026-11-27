module
public import Quantum.FractionalIntercalate

/-! Completing translates of two disjoint cyclic groups gives a Latin
square with a prescribed cyclic subsquare of any admissible smaller size. -/
@[expose] public section
noncomputable section
namespace SudokuSubsquare
open Function Equiv Finset FractionalIntercalate

structure Latin (K I : Type*) [Add K] where
  op : I → I → I
  row : ∀ i, Bijective (op i)
  col : ∀ j, Bijective (fun i => op i j)
  tag : K ↪ I
  sub : ∀ i j, op (tag i) (tag j)=tag (i+j)

def Latin.reindex {K I J : Type*} [Add K] (s : Latin K I) (e : I≃J) : Latin K J where
  op i j := e (s.op (e.symm i) (e.symm j))
  row i := e.bijective.comp ((s.row _).comp e.symm.bijective)
  col j := e.bijective.comp ((s.col _).comp e.symm.bijective)
  tag := s.tag.trans e.toEmbedding
  sub i j := by simp [s.sub]

def Latin.cyclic (K : Type*) [AddGroup K] : Latin K K where
  op := (·+·)
  row i := (Equiv.addLeft i).bijective
  col j := (Equiv.addRight j).bijective
  tag := Function.Embedding.refl _
  sub _ _ := rfl

def onSum (k m : ℕ) [NeZero k] [NeZero m] (hm : k≤m) : Latin (Fin k) (Fin k ⊕ Fin m) := by
  apply Classical.choice
  classical
  let tag : Fin k ↪ Fin k ⊕ Fin m := ⟨Sum.inl,Sum.inl_injective⟩
  let σ (r : Fin k) : Perm (Fin k ⊕ Fin m) :=
    (Equiv.addLeft r).sumCongr (Equiv.addLeft (Fin.castLE hm r))
  let s := univ.image σ
  have hs : Separated s := by
    intro f hf g hg x he
    obtain ⟨r,_,rfl⟩ := mem_image.mp hf
    obtain ⟨u,_,rfl⟩ := mem_image.mp hg
    congr 1
    cases x with
    | inl a => exact add_right_cancel (Sum.inl.inj he)
    | inr b =>
      have he' : Fin.castLE hm r+b=Fin.castLE hm u+b := Sum.inr.inj he
      have he'' : Fin.castLE hm r=Fin.castLE hm u := add_right_cancel he'
      exact Fin.ext (congrArg (fun i : Fin m => i.val) he'')
  obtain ⟨t,subT,sep,hcard⟩ := completion (tag 0) s hs
  let evalAt (j : Fin k ⊕ Fin m) : t ≃ (Fin k ⊕ Fin m) := Equiv.ofBijective (fun a => a.val j)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a b h => Subtype.ext (sep _ a.2 _ b.2 j h),by simpa using hcard⟩)
  let rowOf (r : Fin k) : t := ⟨σ r,subT (mem_image.mpr ⟨r,mem_univ _,rfl⟩)⟩
  have atZero (r : Fin k) : (evalAt (tag 0)).symm (tag r)=rowOf r := by
    apply (evalAt _).symm_apply_eq.mpr
    change Sum.inl r=Sum.inl (r+0)
    simp
  refine ⟨{op := fun i j => ((evalAt (tag 0)).symm i).val j,
           row := fun i => ((evalAt (tag 0)).symm i).val.bijective,
           col := fun j => (evalAt j).bijective.comp (evalAt (tag 0)).symm.bijective,
           tag := tag,sub := ?_}⟩
  intro r c
  rw [atZero]
  rfl

def ofOrders (k n : ℕ) [NeZero k] (hn : 2*k≤n) : Latin (Fin k) (Fin n) := by
  let m := n-k
  have hm : k≤m := by dsimp [m]; omega
  have : NeZero m := ⟨by have := NeZero.ne k; omega⟩
  exact (onSum k m hm).reindex (finSumFinEquiv.trans (finCongr (by dsimp [m];omega)))

#print axioms ofOrders
end SudokuSubsquare
