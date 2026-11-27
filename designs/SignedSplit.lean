import SignedBasic

/-! Splitting off the prime part of a finite abelian group of order pm when p and m are coprime. -/

noncomputable section

namespace Signed39.Contraction

variable {G : Type} [AddCommGroup G] [Fintype G] {p : ℕ} [Fact p.Prime]

theorem split_prime_factor {m : ℕ} (hm : Fintype.card G=p*m) (hc : p.Coprime m) :
    ∃ K : Subgroup (Multiplicative G), Nat.card K=m ∧ Nonempty (ZMod p × Additive K ≃+ G) := by
  classical
  let M := Multiplicative G
  have cardM : Fintype.card M = Fintype.card G := Fintype.card_congr Multiplicative.toAdd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card (G := M) p (cardM ▸ ⟨m,hm⟩)
  let N := Subgroup.zpowers x
  have cardN : Nat.card N=p := (Nat.card_zpowers x).trans hx
  have card' : Nat.card M = p*m := Nat.card_eq_fintype_card.trans (cardM.trans hm)
  have ind : N.index=m := by
    have hh := N.card_mul_index
    rw [cardN,card'] at hh
    exact Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos hh
  obtain ⟨K,hK⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := N) (by simpa only [cardN,ind] using hc)
  let e₁ : ZMod p ≃+ Additive N :=
    (ZMod.ringEquivCongr cardN.symm).toAddEquiv.trans
      (zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card (show Nat.card (Additive N)=p from cardN)))
  let add : Additive N × Additive K →+ G :=
    { toFun := fun z => (z.1.toMul : M).toAdd + (z.2.toMul : M).toAdd
      map_zero' := by change (0:G)+0=0; simp
      map_add' := by
        intro a b
        change ((a.1.toMul : M).toAdd + (b.1.toMul : M).toAdd) +
          ((a.2.toMul : M).toAdd + (b.2.toMul : M).toAdd) = _
        abel }
  let e₂ : Additive N × Additive K ≃+ G := AddEquiv.ofBijective add hK
  exact ⟨K,hK.symm.index_eq_card.symm.trans ind,⟨(e₁.prodCongr (AddEquiv.refl _)).trans e₂⟩⟩

end Signed39.Contraction
