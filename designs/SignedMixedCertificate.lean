import SignedMixedVariance
import SignedBinaryRow

/-! Iterated separation of row types using an assumed row and its correlations with the remaining rows. -/

namespace Signed39.Contraction

open Finset

abbrev RowType := ℤ × ℤ
structure MixedCut where
  separator : Separator
  bonuses : List ℤ
  multiplier : ℤ

def MixedCut.z (h : MixedCut) (a : ℕ) : ℤ := h.bonuses.getD a 0

def MixedCut.term (p m : ℕ) [NeZero p] (inv : ℤ) (h : MixedCut) (anchor b : RowType) : ℤ :=
  h.separator.value 1 b.1 b.2 (b.1^2) + h.z (b.1 : ZMod p).val
  + h.multiplier*((p:ℤ)*residueCost inv m anchor.1 b.1)

def MixedCut.valid (p m : ℕ) [NeZero p] (k l s c inv : ℤ) (types : List RowType)
    (anchor : RowType) (h : MixedCut) : Prop :=
  0≤h.multiplier ∧ (∀ r : ZMod p, 0≤h.z r.val) ∧
  (h.separator.value p ((p:ℤ)*c) k (k-l+(m:ℤ)*l)+((p/2:ℕ):ℤ)*(∑ r : ZMod p, h.z r.val)
    + h.multiplier*(s*((m:ℤ)*anchor.2-anchor.1^2)) < h.term p m inv anchor anchor) ∧
  ∀ t ∈ types, 0 ≤ h.term p m inv anchor t

instance (p m : ℕ) [NeZero p] (k l s c inv : ℤ) (types : List RowType) (t : RowType) (h : MixedCut) :
    Decidable (h.valid p m k l s c inv types t) := by unfold MixedCut.valid; infer_instance

abbrev Stage := List (RowType × MixedCut)

def remainingTypes (types : List RowType) (stage : Stage) : List RowType :=
  types.filter (fun t => decide (t∉stage.map Prod.fst))

def cascade (p m : ℕ) [NeZero p] (k l s c inv : ℤ) (fin : MixedCut) :
    List Stage → List RowType → Prop
  | [], types =>
      (∀ r : ZMod p, 0≤fin.z r.val) ∧
      fin.separator.value p ((p:ℤ)*c) k (k-l+(m:ℤ)*l) + ((p/2:ℕ):ℤ)*(∑ r : ZMod p, fin.z r.val)<0 ∧
      ∀ t ∈ types, 0≤fin.separator.value 1 t.1 t.2 (t.1^2)+fin.z (t.1:ZMod p).val
  | stage::tail, types =>
      (∀ pair∈stage, pair.2.valid p m k l s c inv types pair.1) ∧
      cascade p m k l s c inv fin tail (remainingTypes types stage)

instance cascadeDec (p m : ℕ) [NeZero p] (k l s c inv : ℤ) (fin : MixedCut) :
    ∀ (stages : List Stage) (types : List RowType), Decidable (cascade p m k l s c inv fin stages types)
  | [], types => by unfold cascade; infer_instance
  | st::rest, types => by
      letI := cascadeDec p m k l s c inv fin rest (remainingTypes types st)
      unfold cascade
      infer_instance

variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {p : ℕ} [Fact p.Prime]

def rowType (f : ZMod p × H → ℤ) (i : ZMod p) : RowType := (rowMass f i,energy (row f i))

theorem sum_separator {k l c : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (hmass : mass f=(p:ℤ)*c) (h : Separator) :
    (∑ i : ZMod p, h.value 1 (rowMass f i) (energy (row f i)) ((rowMass f i)^2))=
    h.value p ((p:ℤ)*c) k (k-l+(Fintype.card H:ℤ)*l) := by
  have sm : (∑ i, rowMass f i)=(p:ℤ)*c := (mass_rowmass f).trans hmass
  have sw : (∑ i, energy (row f i))=k := by simpa [energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  have ss : (∑ i, (rowMass f i)^2)=k-l+(Fintype.card H:ℤ)*l := by
    change energy (rowMass f)=_
    simpa [energy_zero] using rowmass_corr hf 0
  simp only [Separator.value,mul_one,sum_add_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul,
    ← mul_sum,sm,sw,ss]
  ring

theorem excluded_anchor {k l s c inv w : ℤ} {m : ℕ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (hn : k-l=(p:ℤ)*s) (hs : ¬ (p:ℤ)∣s) (hmass : mass f=(p:ℤ)*c)
    (hm : Fintype.card H=m) (hc : p.Coprime m) (hu : (p:ℤ)*inv=1+(m:ℤ)*w)
    {types : List RowType} (hall : ∀ i, rowType f i∈types) {a : RowType} {h : MixedCut}
    (valid : h.valid p m k l s c inv types a) (i : ZMod p) : rowType f i≠a := by
  intro hi
  obtain ⟨pos,zpos,global,localI⟩ := valid
  have lower : h.term p m inv a a ≤ ∑ j : ZMod p, h.term p m inv a (rowType f j) :=
    hi ▸ single_le_sum (fun j _ => localI _ (hall j)) (mem_univ i)
  have capacity := sum_bonus (fun i => (rowMass f i:ZMod p)) h.z zpos (residue_capacity hf hn hs)
  have both := mixed_anchor_bound hf hn hs (hm ▸ hc) (hm ▸ hu) i
  rw [hm] at both
  have aa := congrArg Prod.fst hi
  have bb := congrArg Prod.snd hi
  change rowMass f i=a.1 at aa
  change energy (row f i)=a.2 at bb
  change (p:ℤ)*(∑ j, residueCost inv m (rowMass f i) (rowMass f j))
    ≤ s*((Fintype.card H:ℤ)*energy (row f i)-(rowMass f i)^2) at both
  rw [aa,bb,hm] at both
  have scaled := mul_le_mul_of_nonneg_left both pos
  simp only [MixedCut.term,rowType,sum_add_distrib,← mul_sum,sum_separator hf hmass,hm] at lower
  unfold MixedCut.term at global
  linarith only [lower,global,capacity,scaled]

theorem cascade_sound {k l s c inv w : ℤ} {m : ℕ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (hn : k-l=(p:ℤ)*s) (hs : ¬(p:ℤ)∣s) (hmass : mass f=(p:ℤ)*c)
    (hm : Fintype.card H=m) (hc : p.Coprime m) (hu : (p:ℤ)*inv=1+(m:ℤ)*w)
    {fin : MixedCut} (stages : List Stage) (types : List RowType)
    (hall : ∀i, rowType f i∈types) (hcase : cascade p m k l s c inv fin stages types) : False := by
  induction stages generalizing types with
  | nil =>
      obtain ⟨zpos,bad,all⟩ := hcase
      have cap := sum_bonus (fun i => (rowMass f i:ZMod p)) fin.z zpos (residue_capacity hf hn hs)
      have pos := sum_nonneg (s:=univ) (fun i _ => all _ (hall i))
      simp only [rowType,sum_add_distrib,sum_separator hf hmass,hm] at pos
      linarith only [cap,pos,bad]
  | cons stage tail ih =>
      obtain ⟨valid,rest⟩ := hcase
      apply ih (remainingTypes types stage) _ rest
      intro i
      apply List.mem_filter.mpr
      refine ⟨hall i,decide_eq_true ?_⟩
      intro h
      obtain ⟨⟨t,cut⟩,inside,eq⟩ := List.mem_map.mp h
      exact excluded_anchor hf hn hs hmass hm hc hu hall (valid _ inside) i eq.symm

def mixedCover (p m D q : ℕ) (s l c : ℤ) (types : List RowType) : Prop :=
  ∀ i : Fin (2*D+1), ∀ b : Fin (m+1), let d := (i.val:ℤ)-(D:ℤ)
    let a := c+d; let B := (b.val:ℤ)
    (q:ℤ)∣d → d^2≤((p:ℤ)-1)*s → admissibleRow p m s l c a B →
    admissibleShift p m a B → admissibleFull p m a B → (a,B)∈types

instance (p m D q : ℕ) (s l c : ℤ) (types : List RowType) : Decidable (mixedCover p m D q s l c types) := by
  unfold mixedCover; infer_instance

def mixedCertificate (p m : ℕ) [NeZero p] (k l s c inv w : ℤ)
    (D q e : ℕ) (types : List RowType) (stages : List Stage) (fin : MixedCut) : Prop :=
  p.Prime ∧ p.Coprime m ∧ k-l=(p:ℤ)*s ∧ ¬(p:ℤ)∣s ∧ ((p:ℤ)*c)^2=k-l+((p:ℤ)*m)*l ∧
  deviationModulus p s q e ∧ ((p:ℤ)-1)*s<((D:ℤ)+1)^2 ∧ (p:ℤ)*inv=1+(m:ℤ)*w ∧
  (4*p).Coprime m ∧ Nat.Coprime 4 p ∧ mixedCover p m D q s l c types ∧
  cascade p m k l s c inv fin stages types

instance (p m : ℕ) [NeZero p] (k l s c inv w : ℤ) (D q e : ℕ) (types : List RowType)
    (stages : List Stage) (fin : MixedCut) : Decidable (mixedCertificate p m k l s c inv w D q e types stages fin) := by
  letI := cascadeDec p m k l s c inv fin stages types
  unfold mixedCertificate
  infer_instance

theorem mixed_false {k l s c inv w : ℤ} {m D q e : ℕ} {types : List RowType} {stages : List Stage} {fin : MixedCut}
    (hm : Fintype.card H=m) (cert : mixedCertificate p m k l s c inv w D q e types stages fin) :
    ¬∃ f : ZMod p × H → ℤ, IsSDS k l f := by
  rintro ⟨g,hg⟩
  obtain ⟨_,cop,hn,hs,hc2,hmod,hD,hInv,h4,cp4,cover,rule⟩ := cert
  have msum := sds_mass hg
  rw [Fintype.card_prod,ZMod.card,hm,Nat.cast_mul,←hc2] at msum
  obtain ⟨f,hf,hmain⟩ : ∃ f : ZMod p × H → ℤ, IsSDS k l f ∧ mass f=(p:ℤ)*c := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp msum with h|h
    · exact ⟨g,hg,h⟩
    · exact ⟨fun x=> -g x,hg.neg,by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using h⟩
  apply cascade_sound hf hn hs hmain hm cop hInv stages types _ rule
  intro i
  let a := rowMass f i
  let b := energy (row f i)
  let d := a-c
  obtain ⟨div,sq⟩ := centered_row_bounds hf hn hmain hmod i
  change (q:ℤ)∣d at div
  change d^2≤((p:ℤ)-1)*s at sq
  have low : -(D:ℤ)≤d := by
    by_contra! bad
    nlinarith [mul_nonneg (show 0≤ -(D:ℤ)-1-d by omega) (show 0≤ -d+(D:ℤ)+1 by omega)]
  have high : d≤(D:ℤ) := by
    by_contra! bad
    nlinarith [mul_nonneg (show 0≤d-(D:ℤ)-1 by omega) (show 0≤d+(D:ℤ)+1 by omega)]
  have h₁ := row_admissible hf hn hmain (hm ▸ cop) i
  have h₂ := row_shift_admissible hf hn hs (hm ▸ cop) i
  have h₃ := full_row_admissible hf hn hs (hm ▸ cop) (hm ▸ h4) cp4.isCoprime i
  rw [hm] at h₁ h₂ h₃
  change admissibleRow p m s l c a b at h₁
  change admissibleShift p m a b at h₂
  change admissibleFull p m a b at h₃
  have b₀ := h₁.2.2.1
  have b₁ := h₁.2.2.2.1
  let u : Fin (2*D+1) := ⟨(d+D).toNat,by omega⟩
  let v : Fin (m+1) := ⟨b.toNat,by omega⟩
  have eq₁ : (u.val:ℤ)-(D:ℤ)=d := by dsimp [u]; omega
  have eq₂ : (v.val:ℤ)=b := Int.toNat_of_nonneg b₀
  have ac : c+d=a := by dsimp [d]; ring
  have temp := cover u v
  simp only [eq₁,eq₂,ac] at temp
  exact temp div sq h₁ h₂ h₃

theorem abelian_mixed_exclusion (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p m : ℕ) [NeZero p] (k l s c inv w : ℤ) (D q e : ℕ)
    (types : List RowType) (stages : List Stage) (fin : MixedCut)
    (hg : Fintype.card G=p*m) (cert : mixedCertificate p m k l s c inv w D q e types stages fin) :
    ¬∃ f : G → ℤ, IsSDS k l f := by
  classical
  have : Fact p.Prime := ⟨cert.1⟩
  obtain ⟨H,hH,⟨eq⟩⟩ := split_prime_factor hg cert.2.1
  rintro ⟨f,hf⟩
  have size : Fintype.card (Additive H)=m := Nat.card_eq_fintype_card.symm.trans hH
  exact mixed_false size cert ⟨_,pullback hf eq⟩

#print axioms abelian_mixed_exclusion

end Signed39.Contraction
