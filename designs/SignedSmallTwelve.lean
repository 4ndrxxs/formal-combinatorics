import SignedSmallTwelveRows
import SignedAbsoluteBound

/-! Nonexistence at norm 12 when three divides the abelian group order. -/

namespace Signed39.SmallTwelve

open Finset Signed39.Contraction

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def parameterPossibilities (v h lam : ℤ) : Prop :=
  (v=33 ∧ h=12 ∧ lam=4) ∨ (v=33 ∧ h=21 ∧ lam=13) ∨
  (v=39 ∧ h=18 ∧ lam=8) ∨ (v=39 ∧ h=21 ∧ lam=11) ∨
  (v=69 ∧ h=9 ∧ lam=1) ∨ (v=69 ∧ h=60 ∧ lam=52)

instance (v h l : ℤ) : Decidable (parameterPossibilities v h l) := by unfold parameterPossibilities; infer_instance

private theorem enumerate_parameters : ∀ v h : Fin 158,
    let V : ℤ := v.val
    let h' : ℤ := h.val
    let l := (h'^2-12)/V
    9<V → 3∣V → ¬ 9∣V → ¬ 2∣V → h'^2=12+V*l → h'≤12+l → 12+l≤V →
    2∣12+l-h' → parameterPossibilities V h' l := by decide +kernel

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem prime_second {k lam : ℤ} {f : ZMod 3 × H → ℤ} (hf : IsSDS k lam f) (r : ℕ) [Fact r.Prime]
    (hcard : Fintype.card H=r) : ∃ g : ZMod 3 × ZMod r → ℤ, IsSDS k lam g ∧ mass g=mass f := by
  have hr : Nat.card H=r := Nat.card_eq_fintype_card.trans hcard
  let e := (ZMod.ringEquivCongr hr.symm).toAddEquiv.trans (zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card hr))
  let e' := (AddEquiv.refl (ZMod 3)).prodCongr e
  exact ⟨fun t => f (e' t),pullback hf e',Fintype.sum_equiv e'.toEquiv _ _ (fun _ => rfl)⟩

theorem normalized_false {k lam : ℤ} {f : ZMod 3 × H → ℤ} (hf : IsSDS k lam f)
    (hn : k-lam=12) (hpos : 0 ≤ mass f) (hc : Nat.Coprime 3 (Fintype.card H)) (hm : 3<Fintype.card H) : False := by
  let v := Fintype.card (ZMod 3 × H)
  have hv : v=3*Fintype.card H := by simp [v,Fintype.card_prod,ZMod.card]
  have nsp : ¬ IsSquare (k-lam) := hn ▸ nonsquare_of_valuation_one (p:=3) (s:=4) (by decide) (by decide)
  have upper := absolute_order_bound hf (by omega) nsp
  rw [hn] at upper
  change (v:ℤ)≤12^2+12+1 at upper
  norm_num at upper
  have odd : ¬ 2 ∣ v := fun even => nsp (even_norm_square hf even)
  have nine : ¬ 3 ∣ Fintype.card H := (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mp hc
  have sk := support_card hf
  have kb : k≤(v:ℤ) := by rw [← sk]; exact_mod_cast (card_le_univ _)
  have ns := negative_count hf
  change 2*_=k-mass f at ns
  have z : ∃ q : ℤ, k-mass f=2*q := ⟨_,ns.symm⟩
  have hsmall : mass f≤k := by have h0 : (0:ℤ) ≤ ((univ.filter (fun x => f x= -1)).card:ℤ) := Nat.cast_nonneg _; omega
  let V : Fin 158 := ⟨v,by omega⟩
  let S : Fin 158 := ⟨(mass f).toNat,by omega⟩
  have eqS : (S.val:ℤ)=mass f := Int.toNat_of_nonneg hpos
  have vpos : 0<(v:ℤ) := by omega
  have massid := sds_mass hf
  change (mass f)^2=k-lam+(v:ℤ)*lam at massid
  rw [hn] at massid
  have divide : ((mass f)^2-12)/(v:ℤ)=lam := by
    rw [show (mass f)^2-12=lam*(v:ℤ) by linarith [mul_comm (v:ℤ) lam]]
    exact Int.mul_ediv_cancel _ vpos.ne'
  have cases := enumerate_parameters V S
  change 9<(v:ℤ) → 3∣(v:ℤ) → ¬ 9∣(v:ℤ) → ¬ 2∣(v:ℤ) → _ at cases
  simp only [show V.val=v from rfl,eqS,divide] at cases
  have div3 : (3:ℤ) ∣ (v:ℤ) := ⟨(Fintype.card H:ℤ),by exact_mod_cast hv⟩
  have div9 : ¬ (9:ℤ) ∣ (v:ℤ) := by omega
  have div2 : ¬ (2:ℤ) ∣ (v:ℤ) := by exact_mod_cast odd
  obtain h|h|h|h|h|h := cases (by omega) div3 div9 div2 massid (by omega) (by omega) (by
    rwa [show 12+lam=k by omega])
  all_goals rcases h with ⟨hV,hS,hL⟩
  · have hK : k=16 := by omega
    rw [hK,hL] at hf
    exact local_false (c:=4) hf (by decide) hS (by decide : Nat.Coprime 3 11) (by omega) (by decide +kernel)
  · have hK : k=25 := by omega
    rw [hK,hL] at hf
    exact local_false (c:=7) hf (by decide) hS (by decide : Nat.Coprime 3 11) (by omega) (by decide +kernel)
  · have hK : k=20 := by omega
    rw [hK,hL] at hf
    obtain ⟨g,hg,hgM⟩ := prime_second hf 13 (by omega)
    exact Signed39.Analytic.product_false g hg (hgM.trans hS)
  · have hK : k=23 := by omega
    rw [hK,hL] at hf
    obtain ⟨g,hg,hgM⟩ := prime_second hf 13 (by omega)
    exact product_39_23_false hg (hgM.trans hS)
  · have hK : k=13 := by omega
    rw [hK,hL] at hf
    exact local_false (c:=3) hf (by decide) hS (by decide : Nat.Coprime 3 23) (by omega) (by decide +kernel)
  · have hK : k=64 := by omega
    rw [hK,hL] at hf
    exact local_false (c:=20) hf (by decide) hS (by decide : Nat.Coprime 3 23) (by omega) (by decide +kernel)

theorem product_false {k lam : ℤ} {f : ZMod 3 × H → ℤ} (hf : IsSDS k lam f) (hn : k-lam=12)
    (hc : Nat.Coprime 3 (Fintype.card H)) (hm : 3<Fintype.card H) : False := by
  by_cases hpos : 0 ≤ mass f
  · exact normalized_false hf hn hpos hc hm
  · exact normalized_false hf.neg hn (by simp only [mass,sum_neg_distrib] at hpos ⊢; omega) hc hm

#print axioms product_false

end Signed39.SmallTwelve

