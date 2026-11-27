import SignedProjectedWords
import SignedPrimeClassification

namespace Signed39.Contraction

open Finset

private theorem integral_product_nonneg (z:ℤ) : 0≤z^2-z := by
  by_cases h:0<z
  · nlinarith [mul_nonneg (show 0≤z by omega) (show 0≤z-1 by omega)]
  · nlinarith [mul_nonneg (show 0≤ -z by omega) (show 0≤1-z by omega)]

theorem mass_floor {X:Type} [Fintype X] (w:X→ℤ) : -mass w≤energy w := by
  have part:=sum_le_sum (s:=univ) (fun i _=>show -w i≤(w i)^2 by nlinarith [integral_product_nonneg (-w i)])
  simpa only [sum_neg_distrib,mass,energy] using part

theorem alphabet_defect_two {X:Type} [Fintype X] (w:X→ℤ) (two:energy w-mass w≤2) :
    (∀x,w x= -1 ∨ w x=0 ∨ w x=1) ∨ (∀x,1-w x= -1 ∨ 1-w x=0 ∨ 1-w x=1) := by
  classical
  let D:=fun x=> (w x)^2-w x
  have pos (x:X) : 0≤D x:=integral_product_nonneg _
  have tot:(∑x,D x)≤2 := by simpa only [D,sum_sub_distrib,energy,mass] using two
  have small (x:X) : D x≤2 := (single_le_sum (s:=univ) (f:=D) (fun y _=>pos y) (mem_univ x)).trans tot
  have rng (x:X) : -1≤w x ∧ w x≤2 := by
    have :=small x; change (w x)^2-w x≤2 at this
    constructor <;> nlinarith [sq_nonneg (w x+2),sq_nonneg (w x-3)]
  by_cases h:∃z,w z=2
  · right
    obtain ⟨z,hz⟩:=h
    have dz:D z=2 := by simp [D,hz]
    have erase: (∑i∈univ.erase z,D i)+D z=∑x,D x:=sum_erase_add _ _ (mem_univ z)
    intro x
    by_cases xz:x=z
    · simp [xz,hz]
    · have le:=single_le_sum (s:=univ.erase z) (f:=D) (fun y _=>pos y) (mem_erase.mpr ⟨xz,mem_univ x⟩)
      have eq: D x=0:=by have:=pos x; omega
      have prod:w x*(w x-1)=0:=by dsimp [D] at eq; linear_combination eq
      rcases mul_eq_zero.mp prod with a|a <;> omega
  · left; push Not at h
    intro x; have:=rng x; have:=h x; omega

theorem reduced_399_206 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=399) :
    ¬∃f:G→ℤ,IsSDS 206 31 f := by
  classical
  let : Fact (Nat.Prime 19):=⟨by decide⟩
  let : Fact (Nat.Prime 7):=⟨by decide⟩
  let : Fact (Nat.Prime 5):=⟨by decide⟩
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor (p:=19) (m:=21) hg (by decide)
  have hm:Fintype.card (Additive K)=21 := Nat.card_eq_fintype_card.symm.trans hK
  have htot:Fintype.card (ZMod 19×Additive K)=399:=by rw [Fintype.card_prod,ZMod.card,hm]
  let π:=AddMonoidHom.snd (ZMod 19) (Additive K)
  obtain ⟨u,mu,fu⟩:=normalized_proj_word (pullback hf E) π (fun y=>⟨(0,y),rfl⟩) 399 21 19 175 589 112 htot hm
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨w,mw,fw⟩:=reduced_flat_word (q:=5) u 21 175 589 2 14 7 9 (by exact_mod_cast hm) fu (by simpa using mu)
    (by decide) (by decide) 3 (by decide) (by rw [hm]; decide) (by decide) (by decide)
  have en:energy w=16 := by rw [energy_zero,fw]; norm_num
  have bad {k l:ℤ} {a:Additive K→ℤ} (ha:IsSDS k l a) (hn:k-l=7) : False := by
    have co:=prime_norm_card (p:=7) ha hn (hm ▸ (by decide : 7∣21))
    omega
  rcases alphabet_defect_two w (by rw [en,mw]; decide) with h|h
  · apply bad (k:=16) (l:=9) (a:=w) ⟨h,fun t=>by rw [fw]; split <;> decide⟩ (by decide)
  · let b:=fun x=>1+(-1)*w x
    have cb (t:Additive K) : corr b t=if t=0 then 9 else 2 := by
      rw [corr_affine,fw,mw,hm]; split <;> decide
    exact bad (k:=9) (l:=2) (a:=b) ⟨fun t=>by simpa [b,sub_eq_add_neg] using h t,cb⟩ (by decide)

theorem reduced_507_77 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=507) :
    ¬∃f:G→ℤ,IsSDS 77 2 f := by
  classical
  let : Fact (Nat.Prime 3):=⟨by decide⟩
  let : Fact (Nat.Prime 5):=⟨by decide⟩
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor (p:=3) (m:=169) hg (by decide)
  have hm:Fintype.card (Additive K)=169 := Nat.card_eq_fintype_card.symm.trans hK
  have htot:Fintype.card (ZMod 3×Additive K)=507:=by rw [Fintype.card_prod,ZMod.card,hm]
  let π:=AddMonoidHom.snd (ZMod 3) (Additive K)
  obtain ⟨u,mu,fu⟩:=normalized_proj_word (pullback hf E) π (fun y=>⟨(0,y),rfl⟩) 507 169 3 75 6 33 htot hm
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨w,mw,fw⟩:=reduced_flat_word (q:=5) u 169 75 6 2 (-61) 3 22 (by exact_mod_cast hm) fu (by simpa using mu)
    (by decide) (by decide) 26 (by decide) (by rw [hm]; decide) (by decide) (by decide)
  have en:energy w=25 := by rw [energy_zero,fw]; norm_num
  have low:=mass_floor w; rw [mw,en] at low; omega

#print axioms reduced_399_206
#print axioms reduced_507_77

end Signed39.Contraction

