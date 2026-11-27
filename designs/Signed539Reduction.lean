import SignedUnsigned49

namespace Signed39.Contraction

open Finset

theorem reduced_539_325 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=539) :
    ¬∃f:G→ℤ,IsSDS 325 50 f := by
  classical
  let : Fact (Nat.Prime 11):=⟨by decide⟩
  let : Fact (Nat.Prime 5):=⟨by decide⟩
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor (p:=11) (m:=49) hg (by decide)
  let H:=Additive K
  have hm:Fintype.card H=49:=Nat.card_eq_fintype_card.symm.trans hK
  have htot:Fintype.card (ZMod 11×H)=539:=by rw [Fintype.card_prod,ZMod.card,hm]
  let π:=AddMonoidHom.snd (ZMod 11) H
  obtain ⟨u,mu,fu⟩:=normalized_proj_word (pullback hf E) π (fun y=>⟨(0,y),rfl⟩) 539 49 11 275 550 165 htot hm
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨w,mw,fw⟩:=reduced_flat_word (q:=5) u 49 275 550 0 33 11 22 (by exact_mod_cast hm) fu (by simpa using mu)
    (by decide) (by decide) 21 (by decide) (by rw [hm]; decide) (by decide) (by decide)
  have en:energy w=33:=by rw [energy_zero,fw]; norm_num
  have good (i:H) : 0≤(w i)^2-w i := by
    by_cases h:0<w i
    · nlinarith [mul_nonneg (show 0≤w i by omega) (show 0≤w i-1 by omega)]
    · nlinarith [mul_nonneg (show 0≤ -w i by omega) (show 0≤1-w i by omega)]
  have all : (∑i,((w i)^2-w i))=0 := by
    rw [sum_sub_distrib]; change energy w-mass w=0; rw [en,mw]; decide
  let D:=fun i=>1+(-1)*w i
  have bits (i:H) : D i=0∨D i=1 := by
    have zero:=(sum_eq_zero_iff_of_nonneg (fun i _=>good i)).mp all i (mem_univ _)
    have mult:w i*(w i-1)=0:=by linear_combination zero
    dsimp [D]
    rcases mul_eq_zero.mp mult with h|h <;> omega
  have md:mass D=16 := by
    simp only [D,mass,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,hm,←mul_sum]
    change (49:ℤ)*1+-1*mass w=16; rw [mw]; decide
  apply no_unsigned_49 hm D bits md
  intro t
  rw [corr_affine,hm,mw,fw]
  split <;> decide

#print axioms reduced_539_325

end Signed39.Contraction

