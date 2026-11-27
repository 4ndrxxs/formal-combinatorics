module
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic

/-! Completing a Latin rectangle by perfect matchings produces an order-two
subsquare in a Latin square of every order two or at least four. -/
@[expose] public section
noncomputable section
namespace FractionalIntercalate
open Finset Equiv Function
variable {I J : Type*} [Fintype I] [DecidableEq I]

def Separated (s : Finset (Perm I)) : Prop :=
  ∀ f ∈ s, ∀ g ∈ s, ∀ x, f x=g x → f=g

def available (s : Finset (Perm I)) (x : I) : Finset I :=
  univ \ s.image (fun f => f x)

theorem mem_available (s : Finset (Perm I)) (x y : I) :
    y∈available s x ↔ ∀ f∈s, f x≠y := by simp [available]

theorem extend_row (s : Finset (Perm I)) (hs : Separated s) (lt : s.card<Fintype.card I) :
    ∃ f : Perm I, ∀ i, f i∈available s i := by
  classical
  let d := Fintype.card I-s.card
  have row (x : I) : (available s x).card=d := by
    rw [available,card_sdiff_of_subset (subset_univ _),card_image_of_injOn]
    · rfl
    exact fun f hf g hg he => hs _ hf _ hg x he
  let link (x y : I) := y∈available s x
  have column (y : I) : (univ.bipartiteBelow link y).card=d := by
    have he : univ.bipartiteBelow link y=univ \ s.image (fun f => f.symm y) := by
      ext x
      simp only [mem_bipartiteBelow,mem_univ,true_and,link,mem_available,mem_sdiff,mem_image,
        not_exists,not_and]
      apply forall_congr' fun f => forall_congr' fun _ => ?_
      exact not_congr (f.eq_symm_apply.symm.trans eq_comm)
    rw [he,card_sdiff_of_subset (subset_univ _),card_image_of_injOn]
    · rfl
    intro f hf g hg eq
    apply hs f hf g hg (f.symm y)
    change f.symm y=g.symm y at eq
    rw [f.apply_symm_apply,eq,g.apply_symm_apply]
  have hall (A : Finset I) : A.card≤(A.biUnion (available s)).card := by
    let T := A.biUnion (available s)
    apply Nat.le_of_mul_le_mul_right (c:=d) _ (Nat.sub_pos_of_lt lt)
    apply card_mul_le_card_mul link
    · intro x hx
      have he : T.bipartiteAbove link x=available s x := by
        ext y
        simp only [mem_bipartiteAbove,link,and_iff_right_iff_imp]
        exact fun hy => subset_biUnion_of_mem (available s) hx hy
      exact (he ▸ row x).ge
    · intro y _
      rw [←column y]
      exact card_le_card (filter_subset_filter _ (subset_univ A))
  obtain ⟨g,hg,ha⟩ := (all_card_le_biUnion_card_iff_exists_injective (available s)).mp hall
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg),ha⟩

theorem completion (x₀ : I) (s : Finset (Perm I)) (hs : Separated s) :
    ∃ t : Finset (Perm I), s⊆t ∧ Separated t ∧ t.card=Fintype.card I := by
  classical
  let choices : Finset (Finset (Perm I)) := univ.filter (fun t => s⊆t ∧ Separated t)
  have mem (t : Finset (Perm I)) : t∈choices ↔ s⊆t ∧ Separated t := by simp [choices]
  obtain ⟨t,ht,hm⟩ := exists_max_image choices card ⟨s,(mem s).mpr ⟨Subset.rfl,hs⟩⟩
  obtain ⟨subT,sep⟩ := (mem t).mp ht
  refine ⟨t,subT,sep,?_⟩
  have cardLE : t.card≤Fintype.card I := by
    have hc := card_le_univ (t.image (fun g => g x₀))
    rw [card_image_of_injOn (fun f hf g hg h => sep f hf g hg x₀ h)] at hc
    exact hc
  by_contra h
  obtain ⟨u,hu⟩ := extend_row t sep (lt_of_le_of_ne cardLE h)
  have fresh (f : Perm I) (hf : f∈t) (x : I) : f x≠u x :=
    (mem_available t x (u x)).mp (hu x) f hf
  have une : u∉t := fun hu' => fresh u hu' x₀ rfl
  have hsep : Separated (insert u t) := by
    intro f hf g hg x he
    rcases mem_insert.mp hf with ef|hf <;> rcases mem_insert.mp hg with eg|hg
    · exact ef.trans eg.symm
    · exact (fresh g hg x (by simpa [ef] using he.symm)).elim
    · exact (fresh f hf x (by simpa [eg] using he)).elim
    · exact sep f hf g hg x he
  have hi := hm _ ((mem _).mpr ⟨subT.trans (subset_insert _ _),hsep⟩)
  rw [card_insert_of_notMem une] at hi
  omega

structure Latin (I : Type*) where
  op : I → I → I
  row : ∀ i, Bijective (op i)
  col : ∀ j, Bijective (fun i => op i j)
  tag : Fin 2 ↪ I
  sub : ∀ i j, op (tag i) (tag j)=tag (i+j)

def Latin.reindex (s : Latin I) (e : I≃J) : Latin J where
  op i j := e (s.op (e.symm i) (e.symm j))
  row i := e.bijective.comp ((s.row _).comp e.symm.bijective)
  col j := e.bijective.comp ((s.col _).comp e.symm.bijective)
  tag := s.tag.trans e.toEmbedding
  sub i j := by simp [s.sub]

def fromDerangement (tag : Fin 2 ↪ I) (f : Perm I) (hf : ∀ i, f i≠i)
    (swap : ∀ a, f (tag a)=tag (1+a)) : Latin I := by
  apply Classical.choice
  classical
  let s : Finset (Perm I) := {Equiv.refl I,f}
  have hs : Separated s := by
    intro g hg k hk x he
    simp only [s,mem_insert,mem_singleton] at hg hk
    rcases hg with rfl|rfl <;> rcases hk with rfl|rfl
    · rfl
    · exact (hf x he.symm).elim
    · exact (hf x he).elim
    · rfl
  obtain ⟨t,subT,sep,hcard⟩ := completion (tag 0) s hs
  let evalAt (j : I) : t≃I := Equiv.ofBijective (fun a => a.val j)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a b h => Subtype.ext (sep _ a.2 _ b.2 j h),by simpa using hcard⟩)
  let idrow : t := ⟨Equiv.refl I,subT (by simp [s])⟩
  let swaprow : t := ⟨f,subT (by simp [s])⟩
  have id0 : (evalAt (tag 0)).symm (tag 0)=idrow :=
    (evalAt (tag 0)).symm_apply_eq.mpr rfl
  have sw1 : (evalAt (tag 0)).symm (tag 1)=swaprow := by
    apply (evalAt _).symm_apply_eq.mpr
    change tag 1=f (tag 0)
    simpa using (swap 0).symm
  refine ⟨{op := fun i j => ((evalAt (tag 0)).symm i).val j,
           row := fun i => ((evalAt (tag 0)).symm i).val.bijective,
           col := fun j => (evalAt j).bijective.comp (evalAt (tag 0)).symm.bijective,
           tag := tag,sub := ?_}⟩
  intro i j
  fin_cases i
  · change ((evalAt (tag 0)).symm (tag 0)).val (tag j)=tag (0+j)
    rw [id0]; simp [idrow]
  · change ((evalAt (tag 0)).symm (tag 1)).val (tag j)=tag (1+j)
    rw [sw1]; exact swap j

def ofOrders (n : ℕ) (h : n=2 ∨ 4≤n) : Latin (Fin n) := by
  apply Classical.choice
  let k := n-2
  have eq : 2+k=n := by dsimp [k]; omega
  have blockPerm : ∃ f : Perm (Fin k), ∀ x, f x≠x := by
    rcases h with rfl|h
    · exact ⟨Equiv.refl _,fun x => Fin.elim0 x⟩
    · refine ⟨finRotate k,fun x => Equiv.Perm.mem_support.mp ?_⟩
      rw [support_finRotate_of_le (n:=k) (by dsimp [k];omega)]
      exact mem_univ x
  obtain ⟨f,hf⟩ := blockPerm
  let tag : Fin 2 ↪ Fin 2 ⊕ Fin k := ⟨Sum.inl,Sum.inl_injective⟩
  let g : Perm (Fin 2 ⊕ Fin k) := (Equiv.swap (0:Fin 2) 1).sumCongr f
  have hg : ∀ i, g i≠i := by
    rintro (i|i)
    · have hn : ∀ j : Fin 2, (Equiv.swap 0 1) j≠j := by decide +kernel
      exact fun he => hn i (Sum.inl.inj he)
    · simpa [g] using hf i
  have sw (a : Fin 2) : g (tag a)=tag (1+a) := by fin_cases a <;> rfl
  exact ⟨(fromDerangement tag g hg sw).reindex (finSumFinEquiv.trans (finCongr eq))⟩

#print axioms ofOrders
end FractionalIntercalate
