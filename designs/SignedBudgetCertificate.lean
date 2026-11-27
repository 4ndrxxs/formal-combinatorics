import SignedMixedCertificate

/-! Local coefficient budgets and a short arithmetic progression of possible row weights. -/

namespace Signed39.Contraction

open Finset

def rowBudget (p m : ℕ) (k c a b : ℤ) : Prop :=
  b-a≤k-(p:ℤ)*c ∧ b+a≤k+(p:ℤ)*c ∧ (m:ℤ)-b≤(p:ℤ)*m-k
instance (p m : ℕ) (k c a b : ℤ) : Decidable (rowBudget p m k c a b) := by unfold rowBudget; infer_instance

def shortCover (p m D J q : ℕ) (k l s c u : ℤ) (P : RowType → Prop) : Prop :=
  ∀ i : Fin (2*D+1), ∀ j : Fin (J+1), let d := (i.val:ℤ)-(D:ℤ); let a := c+d
    let b := a+2*((-u*(s*a+l*a^2))%(p:ℤ)+(p:ℤ)*j.val)
    (q:ℤ)∣d → d^2≤((p:ℤ)-1)*s → rowBudget p m k c a b →
    admissibleRow p m s l c a b → admissibleShift p m a b → admissibleFull p m a b → P (a,b)
instance (p m D J q : ℕ) (k l s c u : ℤ) (P : RowType → Prop) [DecidablePred P] :
    Decidable (shortCover p m D J q k l s c u P) := by unfold shortCover; infer_instance

def shortHeader (p m D J q e : ℕ) (k l s c u t : ℤ) : Prop :=
  p.Prime ∧ p.Coprime m ∧ k-l=(p:ℤ)*s ∧ ¬(p:ℤ)∣s ∧ ((p:ℤ)*c)^2=k-l+((p:ℤ)*m)*l ∧
  deviationModulus p s q e ∧ ((p:ℤ)-1)*s<((D:ℤ)+1)^2 ∧ (4*p).Coprime m ∧ Nat.Coprime 4 p ∧
  2*s*u=1+(p:ℤ)*t ∧ min (k-(p:ℤ)*c) ((m:ℤ)-c+D)<2*(p:ℤ)*((J:ℤ)+1)
instance (p m D J q e : ℕ) (k l s c u t : ℤ) : Decidable (shortHeader p m D J q e k l s c u t) := by
  unfold shortHeader; infer_instance

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {p : ℕ} [Fact p.Prime]

theorem row_budget {k l s c : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (hn : k-l=(p:ℤ)*s) (hσ : mass f=(p:ℤ)*c) (cop : p.Coprime (Fintype.card H)) (i : ZMod p) :
    rowBudget p (Fintype.card H) k c (rowType f i).1 (rowType f i).2 := by
  let a := rowMass f
  let b (j : ZMod p) := energy (row f j)
  have ha : (∑ j,a j)=(p:ℤ)*c := (mass_rowmass f).trans hσ
  have hb : (∑ j,b j)=k := by simpa [b,energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  have bounds (j : ZMod p) : -b j≤a j ∧ a j≤b j ∧ b j≤(Fintype.card H:ℤ) := by
    have z:=row_admissible hf hn hσ cop j
    exact ⟨z.1,z.2.1,z.2.2.2.1⟩
  have minus := single_le_sum (s:=univ) (f:=fun j=>b j-a j) (fun j _=>by have :=(bounds j).2.1; omega) (mem_univ i)
  have plus := single_le_sum (s:=univ) (f:=fun j=>b j+a j) (fun j _=>by have :=(bounds j).1; omega) (mem_univ i)
  have zero := single_le_sum (s:=univ) (f:=fun j=>(Fintype.card H:ℤ)-b j) (fun j _=>by have :=(bounds j).2.2; omega) (mem_univ i)
  simp only [sum_sub_distrib,sum_add_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul,ha,hb] at minus plus zero
  exact ⟨minus,plus,zero⟩

theorem short_cover_sound {k l s c u t : ℤ} {m D J q e : ℕ} {P : RowType → Prop}
    (hm : Fintype.card H=m) (head : shortHeader p m D J q e k l s c u t)
    (cover : shortCover p m D J q k l s c u P) {f : ZMod p × H → ℤ}
    (hf : IsSDS k l f) (hσ : mass f=(p:ℤ)*c) (i : ZMod p) : P (rowType f i) := by
  obtain ⟨_,cop,hn,hs,_,hmod,hD,h4,cp4,hu,window⟩ := head
  let a := rowMass f i
  let b := energy (row f i)
  let d := a-c
  obtain ⟨dv,sq⟩ := centered_row_bounds hf hn hσ hmod i
  change (q:ℤ)∣d at dv
  change d^2≤((p:ℤ)-1)*s at sq
  have low : -(D:ℤ)≤d := by
    by_contra! bad
    nlinarith [mul_nonneg (show 0≤ -(D:ℤ)-1-d by omega) (show 0≤ -d+(D:ℤ)+1 by omega)]
  have high : d≤(D:ℤ) := by
    by_contra! bad
    nlinarith [mul_nonneg (show 0≤d-(D:ℤ)-1 by omega) (show 0≤d+(D:ℤ)+1 by omega)]
  have raw := row_admissible hf hn hσ (hm ▸ cop) i
  have shift := row_shift_admissible hf hn hs (hm ▸ cop) i
  have full := full_row_admissible hf hn hs (hm ▸ cop) (hm ▸ h4) cp4.isCoprime i
  have budget := row_budget hf hn hσ (hm ▸ cop) i
  rw [hm] at raw shift full budget
  change admissibleRow p m s l c a b at raw
  change admissibleShift p m a b at shift
  change admissibleFull p m a b at full
  change rowBudget p m k c a b at budget
  obtain ⟨_,ab,_,bm,⟨w,hw⟩,⟨v,hv⟩,_⟩ := (show admissibleRow p m s l c a b from raw)
  have positive : 0 < (p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have rem : w≡ -u*(s*a+l*a^2) [ZMOD (p:ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-u*v+t*w,?_⟩
    linear_combination -u*hv+s*u*hw+w*hu
  have wp : 0≤w := by omega
  have quot : 0≤w/(p:ℤ) := Int.ediv_nonneg wp positive.le
  have eq := Int.emod_add_mul_ediv w (p:ℤ)
  have wlim : b-a ≤ min (k-(p:ℤ)*c) ((m:ℤ)-c+D) := le_min budget.1 (by dsimp [d] at low; omega)
  have bound : w/(p:ℤ) < (J:ℤ)+1 := by
    by_contra! bad
    have z := mul_le_mul_of_nonneg_left bad positive.le
    have r := Int.emod_nonneg w positive.ne'
    nlinarith only [wlim,window,eq,z,r,hw]
  let I : Fin (2*D+1) := ⟨(d+D).toNat,by omega⟩
  let K : Fin (J+1) := ⟨(w/(p:ℤ)).toNat,by omega⟩
  have ei : (I.val:ℤ)-(D:ℤ)=d := by dsimp [I]; omega
  have ej : (K.val:ℤ)=w/(p:ℤ) := Int.toNat_of_nonneg quot
  have ac : c+d=a := by dsimp [d]; ring
  have eb : a+2*((-u*(s*a+l*a^2))%(p:ℤ)+(p:ℤ)*(w/(p:ℤ)))=b := by rw [←rem,eq]; omega
  have ans := cover I K
  simp only [ei,ac,ej,eb] at ans
  exact ans dv sq budget raw shift full

def shortLinear (p m D J q e : ℕ) [NeZero p] (k l s c u t : ℤ) (h : MixedCut) : Prop :=
  shortHeader p m D J q e k l s c u t ∧ (∀ r : ZMod p, 0≤h.z r.val) ∧
  h.separator.value p ((p:ℤ)*c) k (k-l+(m:ℤ)*l)+((p/2:ℕ):ℤ)*(∑ r : ZMod p,h.z r.val)<0 ∧
  shortCover p m D J q k l s c u (fun b => 0≤h.separator.value 1 b.1 b.2 (b.1^2)+h.z (b.1:ZMod p).val)
instance (p m D J q e : ℕ) [NeZero p] (k l s c u t : ℤ) (h : MixedCut) :
    Decidable (shortLinear p m D J q e k l s c u t h) := by unfold shortLinear; infer_instance

def shortMixed (p m D J q e : ℕ) [NeZero p] (k l s c u t inv w : ℤ)
    (types : List RowType) (stages : List Stage) (fin : MixedCut) : Prop :=
  shortHeader p m D J q e k l s c u t ∧ (p:ℤ)*inv=1+(m:ℤ)*w ∧
  shortCover p m D J q k l s c u (fun b => b∈types) ∧ cascade p m k l s c inv fin stages types
instance (p m D J q e : ℕ) [NeZero p] (k l s c u t inv w : ℤ) (xs : List RowType) (ss : List Stage) (h : MixedCut) :
    Decidable (shortMixed p m D J q e k l s c u t inv w xs ss h) := by
  letI := cascadeDec p m k l s c inv h ss xs
  unfold shortMixed
  infer_instance

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

private theorem split_normalized {k l c : ℤ} {m : ℕ} {f : G → ℤ} (hf : IsSDS k l f)
    (hg : Fintype.card G=p*m) (cop : p.Coprime m) (massEq : ((p:ℤ)*c)^2=k-l+((p:ℤ)*m)*l)
    (reject : ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H], Fintype.card H=m →
      ∀ (f : ZMod p × H → ℤ), IsSDS k l f → mass f=(p:ℤ)*c → False) : False := by
  classical
  obtain ⟨K,hK,⟨eq⟩⟩ := split_prime_factor hg cop
  let H := Additive K
  have size : Fintype.card H=m := Nat.card_eq_fintype_card.symm.trans hK
  have h := pullback hf eq
  have am := sds_mass h
  rw [Fintype.card_prod,ZMod.card,size,Nat.cast_mul,←massEq] at am
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp am with pos|neg
  · exact reject H size _ h pos
  · exact reject H size _ h.neg (by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using neg)

theorem abelian_short_linear (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p m D J q e : ℕ) [NeZero p] (k l s c u t : ℤ) (h : MixedCut) (hg : Fintype.card G=p*m)
    (cert : shortLinear p m D J q e k l s c u t h) : ¬∃ f : G → ℤ, IsSDS k l f := by
  rintro ⟨f,hf⟩
  obtain ⟨head,zpos,bad,cover⟩ := cert
  have : Fact p.Prime := ⟨head.1⟩
  apply split_normalized hf hg head.2.1 head.2.2.2.2.1
  intro H _ _ _ hm g hG hσ
  have loc := sum_nonneg (s:=univ) (fun i _ => short_cover_sound hm head cover hG hσ i)
  have cap := sum_bonus (fun i=>(rowMass g i:ZMod p)) h.z zpos (residue_capacity hG head.2.2.1 head.2.2.2.1)
  simp only [rowType,sum_add_distrib,sum_separator hG hσ,hm] at loc
  linarith only [loc,cap,bad]

theorem abelian_short_mixed (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p m D J q e : ℕ) [NeZero p] (k l s c u t inv w : ℤ) (types : List RowType) (ss : List Stage) (h : MixedCut)
    (hg : Fintype.card G=p*m) (cert : shortMixed p m D J q e k l s c u t inv w types ss h) :
    ¬∃ f : G → ℤ, IsSDS k l f := by
  rintro ⟨f,hf⟩
  obtain ⟨head,hi,cover,valid⟩ := cert
  have : Fact p.Prime := ⟨head.1⟩
  apply split_normalized hf hg head.2.1 head.2.2.2.2.1
  intro H _ _ _ hm g hG hσ
  exact cascade_sound hG head.2.2.1 head.2.2.2.1 hσ hm head.2.1 hi ss types
    (short_cover_sound hm head cover hG hσ) valid

#print axioms abelian_short_mixed
#print axioms abelian_short_linear

end Signed39.Contraction
