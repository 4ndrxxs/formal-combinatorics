import SignedCenteredCertificate

/-! At (559,118,1), a tight row inequality forces an impossible integral multiplicity. -/

namespace Signed39.FiveFiftyNine

open Finset Signed39.Contraction

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

private def score (a b : ℤ) : ℤ := -78-26*a+9*b+a^2+(if a=0 then 78 else 0)

private theorem quality : ∀ u : Fin 21, ∀ w : Fin 44, let a := (u.val:ℤ)-8
    let b := (w.val:ℤ)
    admissibleRow 13 43 9 1 2 a b → admissibleShift 13 43 a b →
    0 ≤ score a b ∧ (score a b=0 →
      (a=0 ∧ b=0) ∨ (a=2 ∧ b=14) ∨ (a=6 ∧ b=22) ∨ (a=11 ∧ b=27)) := by decide +kernel

private theorem product_false {f : ZMod 13 × H → ℤ} (hH : Fintype.card H=43)
    (hf : IsSDS 118 1 f) (hmass : mass f=26) : False := by
  let a := rowMass f
  let b := fun i => energy (row f i)
  have hc : Nat.Coprime 13 (Fintype.card H) := hH ▸ (by decide : Nat.Coprime 13 43)
  have hn : (118:ℤ)-1=(13:ℤ)*9 := by decide
  have q (i : ZMod 13) : 0 ≤ score (a i) (b i) ∧ (score (a i) (b i)=0 →
      (a i=0 ∧ b i=0) ∨ (a i=2 ∧ b i=14) ∨ (a i=6 ∧ b i=22) ∨ (a i=11 ∧ b i=27)) := by
    have de := (centered_row_bounds (c:=2) hf hn hmass (q:=1) (e:=0) (Or.inl rfl) i).2
    change (a i-2)^2≤108 at de
    have lo : -8≤a i := by
      by_contra! h
      have : a i≤ -9 := by omega
      nlinarith [sq_nonneg (a i+9)]
    have hi : a i≤12 := by
      by_contra! h
      have : 13≤a i := by omega
      nlinarith [sq_nonneg (a i-13)]
    have h₁ := row_admissible (c:=2) hf hn hmass hc i
    have h₂ := row_shift_admissible hf hn (by decide) hc i
    rw [hH] at h₁ h₂
    change admissibleRow 13 43 9 1 2 (a i) (b i) at h₁
    change admissibleShift 13 43 (a i) (b i) at h₂
    let u : Fin 21 := ⟨(a i+8).toNat,by omega⟩
    have b0 := h₁.2.2.1
    have bM := h₁.2.2.2.1
    let w : Fin 44 := ⟨(b i).toNat,by omega⟩
    have ev : (u.val:ℤ)-8=a i := by dsimp [u]; omega
    have ew : (w.val:ℤ)=b i := Int.toNat_of_nonneg b0
    have core := quality u w
    simp only [ev,ew] at core
    exact core h₁ h₂
  let Z := univ.filter (fun i : ZMod 13 => a i=0)
  have cap := residue_capacity hf hn (by decide) 0
  have sub : Z⊆univ.filter (fun i : ZMod 13 => (rowMass f i : ZMod 13)=0) := by
    intro i hi
    have t : rowMass f i=0 := (mem_filter.mp hi).2
    simp [t]
  have cap6 : Z.card≤6 := by have h := card_le_card sub; omega
  have sm : (∑ i,a i)=26 := (mass_rowmass f).trans hmass
  have sw : (∑ i,b i)=118 := by simpa [b,energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  have ss : (∑ i,(a i)^2)=160 := by
    change energy (rowMass f)=_
    simpa [energy_zero,hH] using rowmass_corr hf 0
  have scale : (∑ i : ZMod 13, if a i=0 then (78:ℤ) else 0)=(Z.card:ℤ)*78 := by simp [sum_ite,Z]
  have S := sum_nonneg (s:=univ) (fun i _ => (q i).1)
  have explicit : (∑ i : ZMod 13, score (a i) (b i))= -468+(Z.card:ℤ)*78 := by
    simp only [score,sum_add_distrib,sum_sub_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul,← mul_sum,
      sm,sw,ss,scale]
    norm_num
  rw [explicit] at S
  have six : Z.card=6 := by omega
  have zero : (∑ i, score (a i) (b i))=0 := by rw [explicit,six]; norm_num
  have options (i : ZMod 13) := (q i).2
    ((sum_eq_zero_iff_of_nonneg (fun i _ => (q i).1)).mp zero i (mem_univ i))
  let e := fun i : ZMod 13 => if a i=11 then (1:ℤ) else 0
  have eq (i : ZMod 13) : 2*a i-b i+10-(if a i=0 then 10 else 0)=5*e i := by
    rcases options i with ⟨h,j⟩|⟨h,j⟩|⟨h,j⟩|⟨h,j⟩ <;> norm_num [h,j,e]
  have both := congrArg (fun v : ZMod 13 → ℤ => ∑ i, v i) (funext eq)
  change (∑ i : ZMod 13, (2*a i-b i+10-(if a i=0 then 10 else 0)))=∑ i,5*e i at both
  have ten : (∑ i : ZMod 13, if a i=0 then (10:ℤ) else 0)=(Z.card:ℤ)*10 := by simp [sum_ite,Z]
  simp only [sum_add_distrib,sum_sub_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul,← mul_sum,sm,sw,ten,six] at both
  omega

theorem no_abelian_559_118_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=559) : ¬ ∃ f : G → ℤ, IsSDS 118 1 f := by
  classical
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨e⟩⟩ := split_prime_factor (p:=13) (m:=43) hG (by decide)
  have hH : Fintype.card (Additive K)=43 := Nat.card_eq_fintype_card.symm.trans hK
  have h := pullback hf e
  have mass := sds_mass h
  norm_num [Fintype.card_prod,ZMod.card,hH] at mass
  have eq : (Signed39.Contraction.mass (fun x => f (e x)))^2=(26:ℤ)^2 := by simpa using mass
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp eq with hp|hn
  · exact product_false hH h hp
  · exact product_false hH h.neg (by simpa only [Signed39.Contraction.mass,sum_neg_distrib,neg_eq_iff_eq_neg] using hn)

#print axioms no_abelian_559_118_1

end Signed39.FiveFiftyNine

