import SignedLinearPrimeBound

/-! Separating integer inequalities with residue-dependent bounds on row multiplicities. -/

namespace Signed39.Contraction

open Finset

def capacityCertificate (p m : ℕ) [NeZero p] (k lam s c : ℤ) (h : Separator) (bonus : ℕ → ℤ) : Prop :=
  p.Prime ∧ p.Coprime m ∧ k-lam=(p:ℤ)*s ∧ ¬ (p:ℤ) ∣ s ∧
  ((p:ℤ)*c)^2=k-lam+((p:ℤ)*m)*lam ∧
  (∀ r : ZMod p, 0≤bonus r.val) ∧
  h.value p ((p:ℤ)*c) k (k-lam+(m:ℤ)*lam)+((p/2:ℕ):ℤ)*(∑ r : ZMod p, bonus r.val) < 0 ∧
  ∀ u : Fin (2*m+1), ∀ w : Fin (m+1),
    let a := (u.val:ℤ)-(m:ℤ)
    let b := (w.val:ℤ)
    admissibleRow p m s lam c a b → admissibleShift p m a b →
    0≤h.value 1 a b (a^2)+bonus (a:ZMod p).val

instance (p m : ℕ) [NeZero p] (k lam s c : ℤ) (h : Separator) (z : ℕ → ℤ) :
    Decidable (capacityCertificate p m k lam s c h z) := by unfold capacityCertificate; infer_instance

theorem sum_bonus {p : ℕ} [Fact p.Prime] (g : ZMod p → ZMod p) (z : ℕ → ℤ)
    (hz : ∀ r : ZMod p, 0≤z r.val)
    (hcap : ∀ r, 2*(univ.filter (fun i => g i=r)).card ≤ p) :
    (∑ i, z (g i).val) ≤ ((p/2:ℕ):ℤ)*(∑ r : ZMod p, z r.val) := by
  classical
  calc
    _ = ∑ i : ZMod p, ∑ r : ZMod p, if g i=r then z r.val else 0 := by simp
    _ = ∑ r : ZMod p, ((univ.filter (fun i => g i=r)).card:ℤ)*z r.val := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      simp [sum_ite]
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro r _
      apply mul_le_mul_of_nonneg_right _ (hz r)
      exact_mod_cast (show (univ.filter (fun i=>g i=r)).card≤p/2 by have := hcap r; omega)

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {p : ℕ} [Fact p.Prime]

theorem capacity_family_false {k lam s c : ℤ} {m : ℕ} {h : Separator} {z : ℕ → ℤ}
    (hm : Fintype.card H=m) (hn : k-lam=(p:ℤ)*s) (hs : ¬ (p:ℤ) ∣ s)
    (hc2 : ((p:ℤ)*c)^2=k-lam+((p:ℤ)*m)*lam) (zpos : ∀ r : ZMod p, 0≤z r.val)
    (hbad : h.value p ((p:ℤ)*c) k (k-lam+(m:ℤ)*lam)+((p/2:ℕ):ℤ)*(∑ r : ZMod p, z r.val)<0)
    (localBound : ∀ {f : ZMod p × H → ℤ}, IsSDS k lam f → mass f=(p:ℤ)*c → ∀ i : ZMod p,
      0≤h.value 1 (rowMass f i) (energy (row f i)) ((rowMass f i)^2)+z (rowMass f i:ZMod p).val) :
    ¬ ∃ f : ZMod p × H → ℤ, IsSDS k lam f := by
  classical
  rintro ⟨g,hg⟩
  have hmass := sds_mass hg
  rw [Fintype.card_prod,ZMod.card,hm,Nat.cast_mul,← hc2] at hmass
  obtain ⟨f,hf,hmain⟩ : ∃ f : ZMod p × H → ℤ, IsSDS k lam f ∧ mass f=(p:ℤ)*c := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hmass with h|h
    · exact ⟨g,hg,h⟩
    · exact ⟨fun x => -g x,hg.neg,by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using h⟩
  let a := rowMass f
  let b := fun i => energy (row f i)
  have row_ok (i : ZMod p) : 0≤h.value 1 (a i) (b i) ((a i)^2)+z (a i:ZMod p).val := localBound hf hmain i
  have sum_a : (∑ i, a i)=(p:ℤ)*c := (mass_rowmass f).trans hmain
  have sum_b : (∑ i, b i)=k := by simpa [b,energy,row,corr,pow_two,Fintype.sum_prod_type] using hf.flat 0
  have sum_aa : (∑ i, (a i)^2)=k-lam+(m:ℤ)*lam := by
    change energy (rowMass f)=_
    simpa only [← energy_zero,ite_true,hm] using rowmass_corr hf 0
  have bound := sum_bonus (fun i => (a i:ZMod p)) z zpos (residue_capacity hf hn hs)
  have all := sum_nonneg (s:=univ) (fun i _ => row_ok i)
  simp only [Separator.value,mul_one,sum_add_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul,
    ← mul_sum,sum_a,sum_b,sum_aa] at all
  unfold Separator.value at hbad
  linarith only [bound,all,hbad]

theorem capacity_false {k lam s c : ℤ} {m : ℕ} {h : Separator} {z : ℕ → ℤ}
    (hm : Fintype.card H=m) (cert : capacityCertificate p m k lam s c h z) :
    ¬ ∃ f : ZMod p × H → ℤ, IsSDS k lam f := by
  classical
  obtain ⟨_,hcop,hn,hs,hc2,zpos,hbad,hall⟩ := cert
  apply capacity_family_false hm hn hs hc2 zpos hbad
  intro f hf hmain i
  let a := rowMass f
  let b := fun i => energy (row f i)
  have hh := row_admissible hf hn hmain (hm ▸ hcop) i
  have disp := row_shift_admissible hf hn hs (hm ▸ hcop) i
  rw [hm] at hh disp
  change admissibleRow p m s lam c (a i) (b i) at hh
  change admissibleShift p m (a i) (b i) at disp
  have hd := hh
  obtain ⟨h₁,h₂,h₃,h₄,_,_,_⟩ := hd
  let u : Fin (2*m+1) := ⟨(a i+m).toNat,by omega⟩
  let w : Fin (m+1) := ⟨(b i).toNat,by omega⟩
  have hu : (u.val:ℤ)-(m:ℤ)=a i := by dsimp [u]; omega
  have hw : (w.val:ℤ)=b i := by dsimp [w]; omega
  have localBound := hall u w
  simp only [hu,hw] at localBound
  exact localBound hh disp

theorem abelian_capacity_exclusion (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (p m : ℕ) [NeZero p] (k lam s c : ℤ) (h : Separator) (z : ℕ → ℤ)
    (hg : Fintype.card G=p*m) (hc : capacityCertificate p m k lam s c h z) :
    ¬ ∃ f : G → ℤ, IsSDS k lam f := by
  classical
  have : Fact p.Prime := ⟨hc.1⟩
  obtain ⟨K,hK,⟨e⟩⟩ := split_prime_factor hg hc.2.1
  rintro ⟨f,hf⟩
  have hm : Fintype.card (Additive K)=m := Nat.card_eq_fintype_card.symm.trans hK
  exact capacity_false hm hc ⟨_,pullback hf e⟩

#print axioms abelian_capacity_exclusion

end Signed39.Contraction

