import SignedRowCorrelation

/-! A proof of nonexistence for (39,20,8) from individual row correlations. -/

namespace Signed39.Analytic

open Finset Signed39.Contraction

theorem sum_three (a : ZMod 3 → ℤ) : (∑ i, a i)=a 0+a 1+a 2 := by
  have hu : (univ : Finset (ZMod 3)) = {0,1,2} := by decide
  rw [hu]
  simp [show (0:ZMod 3)≠1 by decide,show (0:ZMod 3)≠2 by decide,show (1:ZMod 3)≠2 by decide]
  ring

theorem triple_contains_eight (a b c : ℤ) (h : a+b+c=18) (e : a^2+b^2+c^2=116) :
    a=8 ∨ b=8 ∨ c=8 := by
  have sumsq : (a-6)^2+(b-6)^2+(c-6)^2=8 := by linear_combination e-12*h
  have bound (x : ℤ) (hx : (x-6)^2 ≤ 8) : 4 ≤ x ∧ x ≤ 8 := by
    constructor <;> by_contra! he
    · have h1 : 0 ≤ 3-x := by omega
      nlinarith [sq_nonneg (x-3)]
    · have h1 : 0 ≤ x-9 := by omega
      nlinarith [sq_nonneg (x-9)]
  obtain ⟨a1,a2⟩ := bound a (by nlinarith [sq_nonneg (b-6),sq_nonneg (c-6)])
  obtain ⟨b1,b2⟩ := bound b (by nlinarith [sq_nonneg (a-6),sq_nonneg (c-6)])
  have hc : c=18-a-b := by omega
  rw [hc] at e ⊢
  interval_cases a <;> interval_cases b <;> norm_num at *

theorem complement_corr (u : ZMod 13 → ℤ) (t : ZMod 13) :
    corr (fun x => 1-u x) t = 13-2*mass u+corr u t := by
  calc
    _ = ∑ x : ZMod 13, (1-u x-u (x+t)+u x*u (x+t)) := by
      apply sum_congr rfl; intros; ring
    _ = _ := by simp [sum_add_distrib,sum_sub_distrib,sum_translate,mass,corr,ZMod.card]; ring

theorem small_complement_false (w : ZMod 13 → ℤ) (ht : ∀ x, w x=0 ∨ w x=1 ∨ w x=2)
    (hm : mass w=5) (he : energy w=7) (hc : ∀ t, 3 ∣ corr w t-1) : False := by
  let ones := fun x => if w x=1 then (1:ℤ) else 0
  let twos := fun x => if w x=2 then (1:ℤ) else 0
  have entries (x : ZMod 13) : w x=ones x+2*twos x := by
    rcases ht x with h|h|h <;> norm_num [ones,twos,h]
  have squares (x : ZMod 13) : (w x)^2=ones x+4*twos x := by
    rcases ht x with h|h|h <;> norm_num [ones,twos,h]
  have counts := congrArg (fun f : ZMod 13 → ℤ => ∑ x, f x) (funext entries)
  have counts2 := congrArg (fun f : ZMod 13 → ℤ => ∑ x, f x) (funext squares)
  change mass w = ∑ x, (ones x+2*twos x) at counts
  change energy w = ∑ x, (ones x+4*twos x) at counts2
  simp only [hm,he,sum_add_distrib,← mul_sum] at counts counts2
  have hones : ∑ x, ones x=3 := by omega
  obtain ⟨z,hz⟩ : ∃ z, w z=2 := by
    by_contra! hn
    have zero : (∑ x, twos x)=0 := by simp [twos,hn]
    omega
  have hn (x : ZMod 13) : 0 ≤ w x := by rcases ht x with h|h|h <;> omega
  have lower (t : ZMod 13) : 1+(if t=0 then (6:ℤ) else 0)+3*ones (z+t) ≤ corr w t := by
    by_cases hzero : t=0
    · subst t
      simp [ones,hz,← energy_zero,he]
    obtain ⟨q,hq⟩ := hc t
    have hterm : w z*w (z+t) ≤ corr w t :=
      single_le_sum (fun x _ => mul_nonneg (hn x) (hn (x+t))) (mem_univ z)
    rw [hz] at hterm
    rcases ht (z+t) with h|h|h <;> simp [ones,h,hzero] <;> omega
  have hsum := sum_le_sum (s:=univ) (fun t _ => lower t)
  have perm : (∑ t : ZMod 13, ones (z+t))=3 := by
    simpa only [add_comm z,sum_translate] using hones
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one,ZMod.card,
    sum_ite_eq',mem_univ,ite_true, ← mul_sum,perm,← mass_sq] at hsum
  change _ ≤ (mass w)^2 at hsum
  rw [hm] at hsum
  norm_num at hsum

theorem product_false (f : ZMod 3 × ZMod 13 → ℤ) (hf : IsSDS 20 8 f) (hmain : mass f=18) : False := by
  let a := rowMass f
  let b := fun i => energy (row f i)
  have hs : (∑ i, a i)=18 := (mass_rowmass f).trans hmain
  have hs2 : (∑ i, (a i)^2)=116 := by
    change energy (rowMass f)=_
    simpa [← energy_zero,ZMod.card] using rowmass_corr hf 0
  rw [sum_three] at hs hs2
  obtain ⟨i,hi⟩ : ∃ i, a i=8 := by
    rcases triple_contains_eight _ _ _ hs hs2 with h|h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  have nt (j : ZMod 3) (x : ZMod 13) := hf.ternary (j,x)
  have hlean (j : ZMod 3) : 0 ≤ b j-a j := by
    apply sub_nonneg.mpr
    change (∑ x, f (j,x)) ≤ ∑ x, (f (j,x))^2
    exact sum_le_sum (fun x _ => by rcases nt j x with h|h|h <;> norm_num [h])
  have hb : (∑ j, b j)=20 := by
    simpa [b,energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  have h2 : (∑ j, (b j-a j))=2 := by rw [sum_sub_distrib,hb,sum_three,hs]; norm_num
  have hle : b i-a i ≤ 2 := h2 ▸ single_le_sum (fun j _ => hlean j) (mem_univ i)
  have hdiv (t : ZMod 13) := row_corr_dvd hf
    (by decide : (20:ℤ)-8=(3:ℤ)*4) (by decide) i t
  change ∀ t, 3 ∣ 4*corr (row f i) t+8*(a i)^2 at hdiv
  rw [hi] at hdiv
  have h0 := hdiv 0
  rw [← energy_zero] at h0
  change 3 ∣ 4*b i+8*8^2 at h0
  have bi : b i=10 := by have hl := hlean i; omega
  let w := fun x => 1-row f i x
  apply small_complement_false w
  · intro x
    rcases nt i x with h|h|h <;> norm_num [w,row,h]
  · change (∑ x, (1-row f i x))=5
    simp only [sum_sub_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_one]
    change 13-a i=5
    omega
  · rw [energy_zero,complement_corr,← energy_zero]
    change 13-2*a i+b i=7
    omega
  · intro t
    have h := hdiv t
    rw [complement_corr]
    change 3 ∣ 13-2*a i+corr (row f i) t-1
    omega

theorem no_cyclic_39_20_8 : ¬ ∃ f : ZMod 39 → ℤ, IsSDS 20 8 f := by
  rintro ⟨f,hf⟩
  let e := (ZMod.chineseRemainder (by decide : Nat.Coprime 3 13)).toAddEquiv.symm
  have h := pullback hf e
  have m := sds_mass h
  norm_num [Fintype.card_prod,ZMod.card] at m
  have hm : (mass (fun x => f (e x)))^2=(18:ℤ)^2 := by simpa using m
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hm with hp|hn
  · exact product_false _ h hp
  · apply product_false _ h.neg
    simpa [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using hn

#print axioms no_cyclic_39_20_8

end Signed39.Analytic
