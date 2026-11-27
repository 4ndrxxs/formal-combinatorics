import SignedCrossRows
import SignedSmallTwelveRows

/-! A mixed-row argument for the published open cyclic parameters (95,54,9). -/

namespace Signed39.NinetyFive

open Finset Signed39.Contraction

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem entries_of_four {I : Type} [Fintype I] [DecidableEq I] (z : I → ℤ)
    (hm : mass z=0) (he : energy z=4) :
    (∀ i, z i= -1 ∨ z i=0 ∨ z i=1) ∧ (∃ i, z i= -1) ∧ ∃ j, z j=1 := by
  have each (i : I) : z i= -1 ∨ z i=0 ∨ z i=1 := by
    have bound : (z i)^2 ≤ 4 := he ▸ single_le_sum (fun z' _ => sq_nonneg (z z')) (mem_univ i)
    have neq : (z i)^2 ≠ 4 := by
      intro eq
      have e := sum_erase_add univ (fun u => (z u)^2) (mem_univ i)
      change _+_=energy z at e
      have zero : (∑ u ∈ univ.erase i, (z u)^2)=0 := by omega
      have zs : (∑ u ∈ univ.erase i, z u)=0 := sum_eq_zero (fun u hu => by
        have h := (sum_eq_zero_iff_of_nonneg (fun u _ => sq_nonneg (z u))).mp zero u hu
        simpa using h)
      have m := sum_erase_add univ z (mem_univ i)
      change _+_=mass z at m
      rw [zs,hm,zero_add] at m
      simp [m] at eq
    have strict := lt_of_le_of_ne bound neq
    have lo : -1≤z i := by
      by_contra! h
      have : z i≤ -2 := by omega
      nlinarith [sq_nonneg (z i+2)]
    have hi : z i≤1 := by
      by_contra! h
      have : 2≤z i := by omega
      nlinarith [sq_nonneg (z i-2)]
    omega
  refine ⟨each,?_,?_⟩
  · by_contra! none
    have eq (i : I) : (z i)^2=z i := by rcases (each i).resolve_left (none i) with h|h <;> norm_num [h]
    change (∑ i, (z i)^2)=4 at he
    simp only [eq] at he
    change (∑ i,z i)=0 at hm
    omega
  · by_contra! none
    have eq (i : I) : (z i)^2= -z i := by
      rcases each i with h|h|h
      · norm_num [h]
      · norm_num [h]
      · exact False.elim (none i h)
    change (∑ i, (z i)^2)=4 at he
    simp only [eq,sum_neg_distrib] at he
    change (∑ i,z i)=0 at hm
    omega

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

private theorem forced_rows {f : ZMod 5 × H → ℤ} (hH : Fintype.card H=19) (hf : IsSDS 54 9 f)
    (hm : mass f=30) :
    ∃ i j : ZMod 5, rowMass f i=3 ∧ energy (row f i)=11 ∧ rowMass f j=9 ∧ energy (row f j)=9 := by
  have hn : (54:ℤ)-9=(5:ℤ)*9 := by decide
  obtain ⟨c,hc,_,hmass,hcor⟩ := centered_row_corr hf hn
  have c6 : c=6 := by norm_num at hc; omega
  subst c
  let u := fun i => rowMass f i-6
  have div := self_conjugate_centered (q:=3) u hcor 2 (by decide) (by decide) (by decide)
  choose z hz using div
  have form : u=fun i => 3*z i := funext hz
  have zero : mass z=0 := by
    change mass u=0 at hmass
    rw [form] at hmass
    simp only [mass,← mul_sum] at hmass
    change (∑ i,z i)=0
    omega
  have en : energy z=4 := by
    have h : energy u=36 := by rw [energy_zero]; norm_num [u,hcor]
    rw [form,energy_scale] at h
    omega
  obtain ⟨tern,⟨i,hi⟩,⟨j,hj⟩⟩ := entries_of_four z zero en
  let b := fun t => energy (row f t)
  let L := fun t => 14-z t-4*(z t)^2
  have zval (i : ZMod 5) : rowMass f i=6+3*z i := by have h := hz i; dsimp [u] at h; omega
  have check : ∀ u : Fin 3, ∀ w : Fin 20, let z' := (u.val:ℤ)-1
      let a := 6+3*z'
      admissibleRow 5 19 9 9 6 a w.val → admissibleShift 5 19 a w.val → 14-z'-4*z'^2≤w.val := by decide +kernel
  have each (t : ZMod 5) : L t≤b t := by
    have hcop : Nat.Coprime 5 (Fintype.card H) := hH ▸ (by decide : Nat.Coprime 5 19)
    have hull := row_admissible (c:=6) hf hn hm hcop t
    have shift := row_shift_admissible hf hn (by decide) hcop t
    rw [hH] at hull shift
    change admissibleRow 5 19 9 9 6 (rowMass f t) (b t) at hull
    change admissibleShift 5 19 (rowMass f t) (b t) at shift
    have b0 := hull.2.2.1
    have bM := hull.2.2.2.1
    let w : Fin 20 := ⟨(b t).toNat,by omega⟩
    have wv : (w.val:ℤ)=b t := Int.toNat_of_nonneg b0
    have h' := tern t
    let u' : Fin 3 := ⟨(z t+1).toNat,by omega⟩
    have uv : (u'.val:ℤ)-1=z t := by dsimp [u']; omega
    have q := check u' w
    simp only [uv,wv,← zval] at q
    exact q hull shift
  have total : (∑ t, b t)=54 := by simpa [b,energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  have Lsum : (∑ t, L t)=54 := by
    change (∑ t : ZMod 5, (14-z t-4*(z t)^2))=54
    change (∑ t,z t)=0 at zero
    change (∑ t,(z t)^2)=4 at en
    simp [sum_sub_distrib,← mul_sum,zero,en,ZMod.card]
  have attain (t : ZMod 5) : b t=L t := by
    have er : (∑ i, (b i-L i))=0 := by rw [sum_sub_distrib,total,Lsum]; norm_num
    exact sub_eq_zero.mp ((sum_eq_zero_iff_of_nonneg (fun x _ => sub_nonneg.mpr (each x))).mp er t (mem_univ _))
  exact ⟨i,j,by rw [zval,hi]; norm_num,by simpa [L,hi] using attain i,
    by rw [zval,hj]; norm_num,by simpa [L,hj] using attain j⟩

private theorem nine_flat (A : H → ℤ) (hH : Fintype.card H=19) (hb : ∀x, A x=0 ∨ A x=1)
    (ma : mass A=9) (en : energy A=9) (congr : ∀ t, 5∣corr A t-4) :
    ∀ t, corr A t=(if t=0 then 5 else 0)+4 := by
  let c := fun t : H => (if t=0 then (5:ℤ) else 0)+4
  have hpos (x : H) : 0≤A x := by rcases hb x with h|h <;> omega
  have lower (t : H) : c t≤corr A t := by
    by_cases ht : t=0
    · subst t; simp [c,← energy_zero,en]
    · have nn : 0≤corr A t := sum_nonneg (fun x _ => mul_nonneg (hpos x) (hpos (x+t)))
      have h := congr t
      simp only [c,ite_eq_right ht,zero_add]
      omega
  have tot := mass_sq A
  change (mass A)^2=_ at tot
  rw [ma] at tot
  have cs : (∑ t,c t)=81 := by simp [c,sum_add_distrib,hH]
  have zz : (∑ t,(corr A t-c t))=0 := by rw [sum_sub_distrib,← tot,cs]; norm_num
  intro t
  exact sub_eq_zero.mp ((sum_eq_zero_iff_of_nonneg (fun t _ => sub_nonneg.mpr (lower t))).mp zz t (mem_univ t))

theorem product_false {f : ZMod 5 × H → ℤ} (hH : Fintype.card H=19) (hf : IsSDS 54 9 f) (hm : mass f=30) : False := by
  obtain ⟨i,j,ai,bi,aj,bj⟩ := forced_rows hH hf hm
  let u := row f i
  let A := row f j
  have hcop : Nat.Coprime 5 (Fintype.card H) := hH ▸ (by decide : Nat.Coprime 5 19)
  have hn : (54:ℤ)-9=(5:ℤ)*9 := by decide
  have binary := Signed39.SmallTwelve.binary_of_mass_eq_energy A (fun x => hf.ternary (j,x)) (bj.trans aj.symm)
  have Aflat := nine_flat A hH binary aj bj (fun t => by
    have h := row_corr_dvd hf hn hcop j t
    change 5∣9*corr A t+9*(rowMass f j)^2 at h
    rw [aj] at h
    omega)
  let h := matched u A
  have tot : mass h=27 := by
    have e := matched_mass u A
    change mass h=rowMass f i*rowMass f j at e
    rw [ai,aj] at e; exact e
  have energy_h : energy h=91 := by
    have e := matched_energy u A 5 4 Aflat
    change energy h=5*energy (row f i)+4*(rowMass f i)^2 at e
    rw [ai,bi] at e; exact e
  have div (t : H) : 5∣3-h t := by
    have hh := row_cross_dvd hf hn hcop i j (-t)
    rw [ai,aj] at hh
    change 5∣9*cross u A (-t)+9*3*9 at hh
    have d : cross u A (-t)=h t := by simp [cross,h,matched,sub_eq_add_neg]
    rw [d] at hh
    omega
  choose z hz using div
  have val (t : H) : h t=3-5*z t := by have h := hz t; omega
  have sq (t : H) : (h t)^2=9-30*z t+25*(z t)^2 := by rw [val]; ring
  change (∑ t,h t)=27 at tot
  simp only [val,sum_sub_distrib,← mul_sum,sum_const,card_univ,hH,nsmul_eq_mul] at tot
  change (∑ t,(h t)^2)=91 at energy_h
  simp only [sq,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,card_univ,hH,nsmul_eq_mul] at energy_h
  have lb (t : H) : z t≤(z t)^2 := by
    by_contra! bad
    have sharper : (z t)^2≤z t-1 := by omega
    nlinarith [sq_nonneg (2*z t-1)]
  have impossible := sum_le_sum (s:=univ) (fun t _ => lb t)
  omega

theorem no_abelian_95_54_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=95) : ¬ ∃ f : G → ℤ, IsSDS 54 9 f := by
  classical
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨e⟩⟩ := split_prime_factor (p:=5) (m:=19) hG (by decide)
  have size : Fintype.card (Additive K)=19 := Nat.card_eq_fintype_card.symm.trans hK
  have h := pullback hf e
  have m := sds_mass h
  norm_num [Fintype.card_prod,ZMod.card,size] at m
  have eq : (mass (fun x => f (e x)))^2=(30:ℤ)^2 := by simpa using m
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp eq with hpos|hneg
  · exact product_false size h hpos
  · exact product_false size h.neg (by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using hneg)

#print axioms no_abelian_95_54_9

end Signed39.NinetyFive

