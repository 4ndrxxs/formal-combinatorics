import SignedPrimeNorm
import SignedField

/-! Classification of signed difference set parameters when the order k−λ is a
prime factor of the size of the ambient abelian group. -/

noncomputable section

namespace Signed39.Contraction

open Finset

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {p : ℕ} [Fact p.Prime]

theorem prime_norm_not_square_factor {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=p) : ¬ p^2 ∣ Fintype.card G := by
  rintro ⟨m,hm⟩
  have he := sds_mass hf
  rw [hn,hm,Nat.cast_mul,Nat.cast_pow] at he
  have hpr := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hd : (p:ℤ) ∣ (mass f)^2 := ⟨1+(p:ℤ)*m*lam,by rw [he]; ring⟩
  obtain ⟨t,ht⟩ := hpr.dvd_of_dvd_pow hd
  have cancel : (p:ℤ)*(t^2-(m:ℤ)*lam) = 1 := by
    apply mul_left_cancel₀ hpr.ne_zero
    rw [ht] at he
    linear_combination he
  exact hpr.not_dvd_one ⟨_,cancel.symm⟩

theorem prime_norm_card {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=p) (hd : p ∣ Fintype.card G) : Fintype.card G = p := by
  classical
  obtain ⟨m,hm⟩ := hd
  have hp := (Fact.out : p.Prime)
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr (by
    rintro ⟨t,ht⟩
    apply prime_norm_not_square_factor hf hn
    exact ⟨t,by rw [hm,ht]; ring⟩)
  have hmpos : 0 < m := by
    by_contra! h
    have hh := Fintype.card_pos (α := G)
    rw [hm,show m=0 by omega,mul_zero] at hh
    omega
  by_cases hm1 : m=1
  · simp [hm,hm1]
  have hm2 : 1 < m := by omega
  let M := Multiplicative G
  have cardM : Fintype.card M = Fintype.card G := Fintype.card_congr Multiplicative.toAdd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card (G := M) p (cardM ▸ ⟨m,hm⟩)
  let N := Subgroup.zpowers x
  have cardN : Nat.card N=p := (Nat.card_zpowers x).trans hx
  have card' : Nat.card M = p*m := Nat.card_eq_fintype_card.trans (cardM.trans hm)
  have ind : N.index=m := by
    have hh := N.card_mul_index
    rw [cardN,card'] at hh
    exact Nat.eq_of_mul_eq_mul_left hp.pos hh
  obtain ⟨K,hK⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := N) (by simpa only [cardN,ind] using hcop)
  let L := Additive K
  have hcL : Fintype.card L = m :=
    Nat.card_eq_fintype_card.symm.trans (by
      change Nat.card K = m
      exact hK.symm.index_eq_card.symm.trans ind)
  let e₁ : ZMod p ≃+ Additive N :=
    (ZMod.ringEquivCongr cardN.symm).toAddEquiv.trans
      (zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card (show Nat.card (Additive N)=p from cardN)))
  let add : Additive N × L →+ G :=
    { toFun := fun z => (z.1.toMul : M).toAdd + (z.2.toMul : M).toAdd
      map_zero' := by change (0:G)+0=0; simp
      map_add' := by
        intro a b
        change ((a.1.toMul : M).toAdd + (b.1.toMul : M).toAdd) +
          ((a.2.toMul : M).toAdd + (b.2.toMul : M).toAdd) = _
        abel }
  let e₂ : Additive N × L ≃+ G := AddEquiv.ofBijective add hK
  let e := (e₁.prodCongr (AddEquiv.refl L)).trans e₂
  have h := pullback hf e
  exact (no_prime_norm_product h hn (hcL ▸ hcop) (hcL ▸ hm2)).elim

theorem prime_norm_parameters {k lam : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=p) (hd : p ∣ Fintype.card G) :
    Fintype.card G = p ∧ k=(p:ℤ)-1 ∧ lam= -1 ∧ p ≠ 2 := by
  have order := prime_norm_card hf hn hd
  have support := support_card hf
  have hbound : k ≤ (Fintype.card G:ℤ) := by rw [← support]; exact_mod_cast card_le_univ _
  have hsq := sds_mass hf
  rw [hn,order] at hsq
  have hp := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hp' : 0<(p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hl : -1 ≤ lam := by
    by_contra! h
    have neg : (p:ℤ)*(1+lam)<0 := mul_neg_of_pos_of_neg hp' (by omega)
    nlinarith [sq_nonneg (mass f)]
  have hne : lam ≠ 0 := by
    intro h
    rw [h,mul_zero,add_zero,pow_two] at hsq
    exact hp.not_isSquare ⟨_,hsq.symm⟩
  rw [order] at hbound
  have hlam : lam= -1 := by omega
  have hk : k=(p:ℤ)-1 := by omega
  refine ⟨order,hk,hlam,?_⟩
  intro h2
  have hm : mass f = 0 := by rw [hlam,mul_neg_one,add_neg_cancel] at hsq; simpa using hsq
  have hneg := negative_count hf
  change 2*_ = k-mass f at hneg
  rw [hk,h2,hm] at hneg
  omega

theorem prime_norm_exists (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=p) (ho : p ≠ 2) :
    ∃ f : G → ℤ, IsSDS ((p:ℤ)-1) (-1) f := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have h : IsSDS ((p:ℤ)-1) (-1) (quadraticChar (ZMod p)) := by
    constructor
    · intro x
      by_cases hx : x=0
      · simp [hx]
      · rcases quadraticChar_dichotomy hx with h|h <;> simp [h]
    · intro t
      rw [FieldConstruction.character_corr hchar,ZMod.card]
      by_cases ht : t=0 <;> simp [ht]
  have ord : Nat.card G=p := Nat.card_eq_fintype_card.trans hG
  let e : ZMod p ≃+ G := (ZMod.ringEquivCongr ord.symm).toAddEquiv.trans
    (zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card ord))
  exact ⟨_,pullback h e.symm⟩

/-- When n=k−λ is prime and divides |G|, the complete possible parameter set
consists of (p,p−1,−1) for odd p. -/
theorem prime_norm_classification {k lam : ℤ} (hn : k-lam=p) (hd : p ∣ Fintype.card G) :
    (∃ f : G → ℤ, IsSDS k lam f) ↔
    Fintype.card G = p ∧ k=(p:ℤ)-1 ∧ lam= -1 ∧ p ≠ 2 := by
  constructor
  · rintro ⟨f,h⟩
    exact prime_norm_parameters h hn hd
  · rintro ⟨hG,rfl,rfl,ho⟩
    exact prime_norm_exists G hG ho

#print axioms prime_norm_classification

end Signed39.Contraction
