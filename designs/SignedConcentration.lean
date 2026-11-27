import SignedDisplacement
import SignedQuotient

/-! Quantitative concentration of the projected row masses. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {p : ℕ} [Fact p.Prime]

/-- The row masses, centered at the integer global mean, have two-level autocorrelation. -/
theorem centered_row_corr {k lam s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*s) :
    ∃ c : ℤ, mass f=(p:ℤ)*c ∧ (p:ℤ)*c^2=s+(Fintype.card H:ℤ)*lam ∧
      mass (fun i => rowMass f i-c)=0 ∧
      ∀ t : ZMod p, corr (fun i => rowMass f i-c) t=(if t=0 then (p:ℤ)*s else 0)-s := by
  have hpr : (p:ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨c,hc⟩ := mass_dvd hf ⟨s,hn⟩
  change mass f=(p:ℤ)*c at hc
  have h := sds_mass hf
  rw [hc,hn,Fintype.card_prod,ZMod.card,Nat.cast_mul] at h
  have he : (p:ℤ)*c^2=s+(Fintype.card H:ℤ)*lam := by
    apply mul_left_cancel₀ hpr
    linear_combination h
  have hsum : (∑ i, rowMass f i)=(p:ℤ)*c := (mass_rowmass f).trans hc
  refine ⟨c,hc,he,?_,?_⟩
  · simp [mass,sum_sub_distrib,hsum,ZMod.card]
  · intro t
    have ht : (∑ i, rowMass f (i+t)) = (p:ℤ)*c := (sum_translate _ _).trans hsum
    calc
      _ = ∑ i, (rowMass f i*rowMass f (i+t)-c*rowMass f i-c*rowMass f (i+t)+c^2) := by
        apply sum_congr rfl; intros; ring
      _ = corr (rowMass f) t-c*((p:ℤ)*c)-c*((p:ℤ)*c)+(p:ℤ)*c^2 := by
        simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,hsum,ht,sum_const,card_univ,
          nsmul_eq_mul,ZMod.card,corr]
      _ = _ := by rw [rowmass_corr hf,hn]; linear_combination -he

/-- At most s rows have positive variance. -/
theorem constant_row_count {k lam s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s) (hc : p.Coprime (Fintype.card H))
    (hm : 1 < Fintype.card H) :
    (p:ℤ)-s ≤ ((univ.filter (fun i : ZMod p => ∀ x, row f i x = row f i 0)).card:ℤ) := by
  classical
  let m : ℤ := Fintype.card H
  let C := univ.filter (fun i : ZMod p => ∀ x, row f i x = row f i 0)
  let w := (p:ℤ)*(m-1)
  have wpos : 0 < w := mul_pos (by exact_mod_cast (Fact.out : p.Prime).pos) (by dsimp [m]; omega)
  have each (i : ZMod p) : (if i∈C then 0 else w) ≤ variance (row f i) := by
    by_cases h : i∈C
    · simpa [h] using variance_nonneg (row f i)
    · have varying : ¬ ∀ x, row f i x=row f i 0 := by simpa [C] using h
      push Not at varying
      obtain ⟨x,hx⟩ := varying
      simpa [h,w,m] using variation_lower (row f i) hc (row_displacement_dvd hf hn hs hc i) hx
  have low := sum_le_sum (s:=univ) (fun i _ => each i)
  have sum_others : (∑ i : ZMod p, if i∈C then 0 else w) = ((p:ℤ)-(C.card:ℤ))*w := by
    simp [sum_ite,Finset.filter_notMem_eq_sdiff,card_sdiff_of_subset,ZMod.card,Nat.cast_sub,
      show C.card≤p by simpa [ZMod.card] using C.card_le_univ,sub_mul]
  rw [sum_others,total_row_variance hf,hn] at low
  have count : (p:ℤ)-s ≤ (C.card:ℤ) := by
    have h : ((p:ℤ)-(C.card:ℤ))*w ≤ s*w := by convert low using 1; dsimp [w,m]; ring
    have le := le_of_mul_le_mul_right h wpos
    omega
  exact count

/-- At least p-s rows are constant. One such row has a small integral centered mass,
whose square obeys an exact congruence modulo the cofactor. -/
theorem concentration {k lam s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s) (hc : p.Coprime (Fintype.card H))
    (hm : 1 < Fintype.card H) (hsmall : s < (p:ℤ)) {c : ℤ}
    (he : (p:ℤ)*c^2=s+(Fintype.card H:ℤ)*lam)
    (hen : energy (fun i => rowMass f i-c)=((p:ℤ)-1)*s) :
    ∃ i : ZMod p, let d := rowMass f i-c
      ((p:ℤ)-s)*d^2 ≤ ((p:ℤ)-1)*s ∧ (Fintype.card H:ℤ) ∣ (p:ℤ)*d^2-s := by
  classical
  let m : ℤ := Fintype.card H
  let D := fun i : ZMod p => (rowMass f i-c)^2
  let C := univ.filter (fun i : ZMod p => ∀ x, row f i x = row f i 0)
  have count : (p:ℤ)-s ≤ (C.card:ℤ) := constant_row_count hf hn hs hc hm
  have ne : C.Nonempty := card_pos.mp (by omega)
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image C D ne
  have smallsum := sum_le_sum (s:=C) (fun j hj => hmin j hj)
  have upper : ∑ j ∈ C, D j ≤ ∑ j, D j :=
    sum_le_sum_of_subset_of_nonneg (subset_univ C) (fun j _ _ => sq_nonneg _)
  change (∑ j, D j)=_ at hen
  simp only [sum_const,nsmul_eq_mul] at smallsum
  have hle := mul_le_mul_of_nonneg_right count (sq_nonneg (rowMass f i-c))
  change ((p:ℤ)-s)*D i ≤ (C.card:ℤ)*D i at hle
  have hconst : ∀ x, row f i x = row f i 0 := (mem_filter.mp hi).2
  have ha : rowMass f i=m*row f i 0 := by simp [rowMass,mass,hconst,m]
  refine ⟨i,hle.trans (smallsum.trans (upper.trans_eq hen)),?_⟩
  refine ⟨(p:ℤ)*(row f i 0)*(rowMass f i-2*c)+lam,?_⟩
  change (p:ℤ)*(rowMass f i-c)^2-s=m*_
  rw [ha]
  change (p:ℤ)*c^2=s+m*lam at he
  linear_combination he

#print axioms concentration

end Signed39.Contraction

