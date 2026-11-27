import SignedMultiplierOrbits

namespace Signed39.Contraction

open Finset

local instance : Fact (Nat.Prime 103):=⟨by decide⟩

private def times34 : ZMod 103 ≃+ ZMod 103 where
  toFun x:=34*x
  invFun x:=34⁻¹*x
  left_inv x:=by simp only [←mul_assoc,inv_mul_cancel₀ (by decide : (34:ZMod 103)≠0),one_mul]
  right_inv x:=by simp only [←mul_assoc,mul_inv_cancel₀ (by decide : (34:ZMod 103)≠0),one_mul]
  map_add' x y:=by ring

private def W : List ℤ := [0,0,0,0,0,0,0,7,6,2,8,12,15,11,13,4,6,10,2,14,8,5,3,15,6,12,11,2,13,5,10,7,6,16,16,15,2,4,14,11,6,8,13,9,3,2,15,10,6,3,12,8,11,9,2,7,13,14,5,4,10,14,7,9,12,11,5,16,16,15,13,3,8,9,4,12,3,10,11,7,14,4,8,9,13,1,7,5,1,12,10,1,15,9,1,5,4,1,3,14,1,16,16]

private theorem quotient_false (u:ZMod 103→ℤ) (flat:∀t,corr u t=(if t=0 then 161 else 0)+56)
    (mass0:mass u=77) (bound:∀x,-7≤u x ∧ u x≤7) : False := by
  let : Fact (Nat.Prime 7):=⟨by decide⟩
  let : Fact (Nat.Prime 23):=⟨by decide⟩
  have dv (x:ZMod 103) : (161:ℤ)∣matched (fun i=>u (times34.symm i)) u x-56 := by
    change (7:ℤ)*23 ∣ matched (fun i=>u (times34.symm i)) u x-56
    apply (by decide : IsCoprime (7:ℤ) 23).mul_dvd
    · exact prime_multiplier_dvd (q:=7) u 161 56 flat (by decide) (by rw [ZMod.card]; decide)
        times34 3 (fun y=>by change (7^3:ℕ) • y=(34:ZMod 103)*y
                             rw [nsmul_eq_mul,(ZMod.natCast_eq_natCast_iff _ 34 103).mpr (by decide)]; rfl) x
    · exact prime_multiplier_dvd (q:=23) u 161 56 flat (by decide) (by rw [ZMod.card]; decide)
        times34 9 (fun y=>by change (23^9:ℕ) • y=(34:ZMod 103)*y
                             rw [nsmul_eq_mul,(ZMod.natCast_eq_natCast_iff _ 34 103).mpr (by decide)]; rfl) x
  obtain ⟨t,h⟩:=integral_match_translation u 161 56 (by decide) flat times34 dv
  let base:ZMod 103:=25*t
  let g (x:ZMod 103):=u (x+base)
  have ht : 33*base=t := by dsimp [base]; rw [←mul_assoc,show (33:ZMod 103)*25=1 by decide,one_mul]
  have fix (x:ZMod 103) : g (times34 x)=g x := by
    have eq:=h (times34 (x+base))
    rw [times34.symm_apply_apply] at eq
    change u (x+base)=u (34*(x+base)-t) at eq
    change u (34*x+base)=u (x+base)
    rw [show 34*(x+base)-t=34*x+base by linear_combination ht] at eq
    exact eq.symm
  have levels : ∀i:ZMod 103,(17:ℤ)∣(if i=0 then (0:ℤ) else 1)+W.getD (times34 i).val 0-W.getD i.val 0 := by decide +kernel
  have mod:=orbit_mass_dvd times34.toEquiv g (fun i=>W.getD i.val 0) 17 0 fix levels
  have massG : mass g=77 := (sum_translate u base).trans mass0
  change (17:ℤ)∣mass g-u (0+base) at mod
  rw [massG,zero_add] at mod
  have hi:=bound base
  omega

theorem no_721_169_8 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=721) :
    ¬∃f:G→ℤ, IsSDS 169 8 f := by
  classical
  let : Fact (Nat.Prime 103):=⟨by decide⟩
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor (p:=103) (m:=7) hg (by decide)
  have hm : Fintype.card (Additive K)=7 := Nat.card_eq_fintype_card.symm.trans hK
  let F:=fun x=>f (E x)
  have hF:IsSDS 169 8 F:=pullback hf E
  have sq:=sds_mass hF
  rw [Fintype.card_prod,ZMod.card,hm] at sq
  have sq' : (mass F)^2=77^2 := by norm_num at sq ⊢; exact sq
  obtain ⟨g,hg,mg⟩ : ∃g:ZMod 103 × Additive K→ℤ,IsSDS 169 8 g ∧ mass g=77 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp sq' with pos|neg
    · exact ⟨F,hF,pos⟩
    · exact ⟨fun x=> -F x,hF.neg,by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using neg⟩
  apply quotient_false (rowMass g) (fun t=>by simpa [hm] using rowmass_corr hg t) ((mass_rowmass g).trans mg)
  intro i
  have le := sum_le_sum (s:=univ) (fun t _=>show g (i,t)≤1 by rcases hg.ternary (i,t) with h|h|h <;> omega)
  have ge := sum_le_sum (s:=univ) (fun t _=>show -1≤g (i,t) by rcases hg.ternary (i,t) with h|h|h <;> omega)
  simp only [sum_const,card_univ,nsmul_eq_mul,hm,Nat.cast_ofNat] at le ge
  exact ⟨by change _≤∑t,g (i,t); linarith,by change (∑t,g (i,t))≤_; linarith⟩

#print axioms no_721_169_8

end Signed39.Contraction
