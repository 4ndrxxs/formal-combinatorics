import SignedSmallCoefficients
import SignedSmallTwelve
import SignedPrimeClassification

/-! Exact classification when a common prime occurs once in the norm and its cofactor in the norm is at most four. -/

namespace Signed39.Contraction

open Finset

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {p : ℕ} [Fact p.Prime]

/-- If p divides the order of a finite abelian group and divides k−λ exactly once,
the quotient (k−λ)/p cannot be 2, 3, or 4. -/
theorem no_small_norm_cofactor {k lam s : ℤ} {f : G → ℤ} (hf : IsSDS k lam f)
    (hd : p ∣ Fintype.card G) (hn : k-lam=(p:ℤ)*s)
    (hs : ¬ (p:ℤ) ∣ s) (hlo : 2 ≤ s) (hhi : s ≤ 4) : False := by
  classical
  have prime : p.Prime := Fact.out
  have nsp : ¬ IsSquare (k-lam) := hn ▸ nonsquare_of_valuation_one prime hs
  have odd : ¬ 2∣Fintype.card G := fun he => nsp (even_norm_square hf he)
  have hp : 3≤p := by
    by_contra! h
    have h' := prime.two_le
    exact odd ((show p=2 by omega) ▸ hd)
  obtain ⟨m,hcard⟩ := hd
  have cp := valuation_one_coprime hf hcard hn hs
  have hm : 1 < m := by
    by_contra! small
    have gpos := Fintype.card_pos (α:=G)
    have m1 : m=1 := by
      rcases (show m=0 ∨ m=1 by omega) with e|e
      · simp [e] at hcard
      · exact e
    have order : Fintype.card G=p := by simpa only [m1,mul_one] using hcard
    have support := support_card hf
    have kbound : k≤(p:ℤ) := by rw [← order,← support]; exact_mod_cast card_le_univ _
    have he := sds_mass hf
    rw [order] at he
    have hl : -1 ≤ lam := by
      by_contra! bad
      have le : (p:ℤ)-1>0 := by omega
      have be := mul_le_mul_of_nonneg_left (show lam≤ -2 by omega) le.le
      nlinarith [sq_nonneg (mass f)]
    have nn := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg p : 0≤(p:ℤ))
    omega
  have greater := abelian_cofactor_bound hf hcard hm hn hs
  obtain ⟨K,hK,⟨e⟩⟩ := split_prime_factor hcard cp
  have eq : Fintype.card (Additive K)=m := Nat.card_eq_fintype_card.symm.trans hK
  have cop : p.Coprime (Fintype.card (Additive K)) := eq ▸ cp
  have bigger : p < Fintype.card (Additive K) := eq ▸ greater
  have oddK : Odd (Fintype.card (Additive K)) := by
    apply Nat.not_even_iff_odd.mp
    rintro ⟨t,ht⟩
    exact odd ⟨p*t,by rw [hcard,← eq,ht]; ring⟩
  have h := pullback hf e
  rcases (show s=2 ∨ s=3 ∨ s=4 by omega) with l|l|l
  · subst s
    exact no_norm_twice h hn cop hp bigger
  · subst s
    have hp5 : 5≤p := by
      by_contra! hh
      rcases (show p=3 ∨ p=4 by omega) with h3|h4
      · subst p; exact hs (dvd_refl _)
      · exact (by decide : ¬ Nat.Prime 4) (h4 ▸ prime)
    exact no_norm_thrice h hn cop hp5 bigger
  · subst s
    by_cases h3 : p=3
    · subst p
      exact Signed39.SmallTwelve.product_false h hn cop bigger
    · have hp5 : 5≤p := by
        by_contra! hh
        exact (by decide : ¬ Nat.Prime 4) ((show p=4 by omega) ▸ prime)
      exact no_norm_four_times_large h hn cop hp5 bigger oddK

/-- The only possible parameters with 1≤(k−λ)/p≤4 and valuation one at p
are exactly the quadratic-character parameters at the odd prime order p. -/
theorem small_norm_cofactor_classification {k lam s : ℤ} (hd : p ∣ Fintype.card G)
    (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s) (hlo : 1 ≤ s) (hhi : s ≤ 4) :
    (∃ f : G → ℤ, IsSDS k lam f) ↔
    s=1 ∧ Fintype.card G=p ∧ k=(p:ℤ)-1 ∧ lam= -1 ∧ p ≠ 2 := by
  constructor
  · rintro ⟨f,hf⟩
    have eq : s=1 := by
      by_contra h
      exact no_small_norm_cofactor hf hd hn hs (by omega) hhi
    exact ⟨eq,prime_norm_parameters hf (by simpa [eq] using hn) hd⟩
  · rintro ⟨_,hg,rfl,rfl,ho⟩
    exact prime_norm_exists G hg ho

#print axioms no_small_norm_cofactor
#print axioms small_norm_cofactor_classification

end Signed39.Contraction

