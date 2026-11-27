import Quantum.Hadamard.InvolutionBlocks

/-! Every involution splits a finite index set into singletons and paired
orbits. Conjugation-invariance of a sign matrix supplies precisely the five
blocks of the inflation lemma, with no assumption on the fixed-set size. -/
noncomputable section
namespace HadamardMod.InvolutionStretch
variable {X : Type} [Fintype X]

private abbrev Fixed (σ : X ≃ X) := {x : X // σ x=x}

private def first (σ : X ≃ X) (x : X) : Prop :=
  Fintype.equivFin X x < Fintype.equivFin X (σ x)

private abbrev PairRep (σ : X ≃ X) := {x : X // first σ x}

private def decode (σ : X ≃ X) : Index (Fixed σ) (PairRep σ) Bool → X
  | .inl f => f.val
  | .inr (p,false) => p.val
  | .inr (p,true) => σ p.val

private def encode (σ : X ≃ X) (twice : ∀ x, σ (σ x)=x) (x : X) :
    Index (Fixed σ) (PairRep σ) Bool := by
  classical
  by_cases fixed : σ x=x
  · exact .inl ⟨x,fixed⟩
  by_cases before : first σ x
  · exact .inr (⟨x,before⟩,false)
  · have after : first σ (σ x) := by
      unfold first at before ⊢
      rw [twice]
      exact lt_of_le_of_ne (not_lt.mp before) (fun eq => fixed ((Fintype.equivFin X).injective eq))
    exact .inr (⟨σ x,after⟩,true)

private def orbitEquiv (σ : X ≃ X) (twice : ∀ x, σ (σ x)=x) :
    Index (Fixed σ) (PairRep σ) Bool ≃ X where
  toFun := decode σ
  invFun := encode σ twice
  left_inv := by
    classical
    rintro (f | ⟨p,b⟩)
    · simp [decode,encode,f.property]
    · have nf : σ p.val≠p.val := by
        intro h
        have lt := p.property
        simp [first,h] at lt
      have rev : ¬ first σ (σ p.val) := by
        unfold first
        rw [twice]
        exact not_lt_of_gt p.property
      cases b
      · simp [decode,encode,nf,p.property]
      · simp [decode,encode,twice,nf,Ne.symm nf,rev]
  right_inv := by
    classical
    intro x
    by_cases f : σ x=x
    · simp [encode,decode,f]
    · by_cases h : first σ x <;> simp [encode,decode,f,h,twice]

private def orbitBlocks {m : ℕ} (σ : X ≃ X) (H : RowMatrix m X) :
    Blocks m (Fixed σ) (PairRep σ) where
  fixedFixed f g := H f g
  fixedPair f u := H f u
  pairFixed u f := H u f
  equal u v := H u v
  unequal u v := H u (σ v)

private theorem orbit_entry {m : ℕ} (σ : X ≃ X) (twice : ∀ x, σ (σ x)=x)
    (H : RowMatrix m X) (inv : ∀ i j, H (σ i) (σ j)=H i j)
    (i j : Index (Fixed σ) (PairRep σ) Bool) :
    (orbitBlocks σ H).entry i j = H (decode σ i) (decode σ j) := by
  have alongF (f : Fixed σ) (x : X) : H f (σ x)=H f x := by
    simpa only [f.property] using inv f x
  have alongG (x : X) (f : Fixed σ) : H (σ x) f=H x f := by
    simpa only [f.property] using inv x f
  have crossed (x y : X) : H (σ x) y=H x (σ y) := by
    simpa only [twice] using inv x (σ y)
  rcases i with f | ⟨u,a⟩ <;> rcases j with g | ⟨v,b⟩
  · rfl
  · cases b <;> simp [orbitBlocks,Blocks.entry,decode,alongF]
  · cases a <;> simp [orbitBlocks,Blocks.entry,decode,alongG]
  · cases a <;> cases b <;> simp [orbitBlocks,Blocks.entry,decode,inv,crossed,twice]

/-- For an invariant modular Hadamard matrix, retain every fixed index and
replace each of the k transposed pairs by Q indices. -/
theorem inflate_involution {m Q : ℕ} (σ : X ≃ X) (twice : ∀ x, σ (σ x)=x)
    (H : RowMatrix m X) (good : Good H) (inv : ∀ i j, H (σ i) (σ j)=H i j)
    (pos : 0<Q) (two : (Q : ZMod m)=2) :
    ∃ k : ℕ, Nat.card {i : X // σ i=i}+2*k=Fintype.card X ∧
      AtOrder m (Nat.card {i : X // σ i=i}+k*Q) := by
  classical
  letI : Inhabited (Fin Q) := ⟨⟨0,pos⟩⟩
  let e := orbitEquiv σ twice
  let B := orbitBlocks σ H
  have original : Good (B.entry (C:=Bool)) := by
    have same : B.entry (C:=Bool) = fun i j => H (e i) (e j) := by
      funext i j
      exact orbit_entry σ twice H inv i j
    rw [same]
    exact good.transport e
  refine ⟨Fintype.card (PairRep σ),?_,?_⟩
  · have card := Fintype.card_congr e
    simpa [Index,Fixed,Nat.card_eq_fintype_card,Nat.mul_comm] using card
  · apply of_card (B.inflate original (Fin Q) (by simpa using two))
    simp [Index,Fixed,Nat.card_eq_fintype_card]

#print axioms inflate_involution
end HadamardMod.InvolutionStretch
