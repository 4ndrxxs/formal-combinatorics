import SignedFibreMultiplier
import SignedFullConjugacy

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {p : ℕ} [Fact p.Prime]

private def doubleEquiv (hn : (2:ZMod p)≠0) : ZMod p ≃+ ZMod p where
  toFun x:=2*x
  invFun x:=2⁻¹*x
  left_inv x:=by simp only [←mul_assoc,inv_mul_cancel₀ hn,one_mul]
  right_inv x:=by simp only [←mul_assoc,mul_inv_cancel₀ hn,one_mul]
  map_add' x y:=by ring

theorem square_of_double_match {k l:ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (nz : (2:ZMod p)≠0) (cyc : ∀x:ZMod p,x=0∨∃j:Fin p,(2:ZMod p)^j.val=x)
    (t : ZMod p × H) (matchEq : ∀x,f (((doubleEquiv nz).prodCongr (AddEquiv.refl H)).symm x)=f (x-t)) :
    ∃z:ℤ,z^2=k-l := by
  let A:=rowMass f
  have orbit (i:ZMod p) : A i=A (2*i-t.1) := by
    have pt (x:H) : f (i,x)=f (2*i-t.1,x-t.2) := by
      let E:=(doubleEquiv nz).prodCongr (AddEquiv.refl H)
      have e:=matchEq (E (i,x))
      change f (E.symm (E (i,x)))=f (2*i-t.1,x-t.2) at e
      rwa [E.symm_apply_apply] at e
    calc
      _=∑x:H,f (2*i-t.1,x-t.2) := sum_congr rfl (fun x _=>pt x)
      _=_ := by simpa [A,rowMass,row,mass,sub_eq_add_neg] using sum_translate (fun x=>f (2*i-t.1,x)) (-t.2)
  let g (i:ZMod p):=A (i+t.1)
  have same (i:ZMod p) : g i=g (2*i) := by simpa [g,show 2*(i+t.1)-t.1=2*i+t.1 by ring] using orbit (i+t.1)
  have samePow (j:ℕ) : g ((2:ZMod p)^j)=g 1 := by
    induction j with
    | zero=>simp
    | succ j ih=>rw [pow_succ,mul_comm,←same,ih]
  have off (x:ZMod p) (o:x≠0) : g x=g 1 := by
    rcases cyc x with h|⟨j,e⟩
    · exact (o h).elim
    · rw [←e,samePow]
  have co (i:ZMod p) : corr g i=corr A i := by
    simpa [corr,g,add_assoc,add_left_comm,add_comm] using
      sum_translate (fun x:ZMod p=>A x*A (x+i)) t.1
  have diff : corr g 0-corr g 1=k-l := by rw [co,co]; dsimp only [A]; rw [rowmass_corr hf,rowmass_corr hf]; simp
  let z:=g 0-g 1
  have point (x:ZMod p) : (g x-g (x+1))^2=(if x=0 then z^2 else 0)+(if x= -1 then z^2 else 0) := by
    by_cases z0:x=0
    · simp [z0,z]
    by_cases neg:x= -1
    · simp [neg,z,off (-1) (neg_ne_zero.mpr one_ne_zero)]
      ring
    have x1:x+1≠0 := fun h=>neg (eq_neg_of_add_eq_zero_left h)
    simp [z0,neg,off x z0,off (x+1) x1]
  have di:=displacement_squares g 1
  simp only [point,sum_add_distrib,sum_ite_eq',mem_univ,ite_true,displacement,energy_zero,diff] at di
  exact ⟨z,by linarith⟩

theorem binary_fibre_exclusion {k l:ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (j a b : ℕ) (bp:0<b) (hn:k-l=(p:ℤ)*2^j) (hs:¬(p:ℤ)∣(2:ℤ)^j)
    (nz : (2:ZMod p)≠0) (cyc : ∀x:ZMod p,x=0∨∃j:Fin p,(2:ZMod p)^j.val=x)
    (long:p^2<Fintype.card H) (ph:p.Coprime (Fintype.card H))
    (cop : IsCoprime ((2:ℤ)^j) (Fintype.card (ZMod p × H):ℤ))
    (cp : 2^a ≡ 2 [MOD p]) (ch : 2^a ≡ 1 [MOD Fintype.card H])
    (id : 2^b ≡ 1 [MOD Fintype.card (ZMod p × H)]) : False := by
  let A:=doubleEquiv nz
  let E:=A.prodCongr (AddEquiv.refl H)
  have identity {G:Type} [AddCommGroup G] [Fintype G] (c:ℕ) (h : c ≡ 1 [MOD Fintype.card G]) (x:G) : c • x=x :=
    (nsmul_eq_nsmul_iff_modEq.mpr (h.of_dvd (addOrderOf_dvd_card (x:=x)))).trans (one_nsmul _)
  have act (x:ZMod p × H) : 2^a • x=E x := by
    apply Prod.ext
    · change (2^a:ℕ) • x.1=(2:ZMod p)*x.1
      rw [nsmul_eq_mul,(ZMod.natCast_eq_natCast_iff _ _ _).mpr cp]
      rfl
    · exact identity _ ch x.2
  have flat (x:ZMod p × H) : corr f x=(if x=0 then k-l else 0)+l := by rw [hf.flat]; split <;> omega
  let T:=fun x=>matched (fun y=>f (E.symm y)) f x-l
  have ds (x:ZMod p × H) : (2:ℤ)^j∣T x := binary_multiplier_dvd f _ _ flat j a b bp
    (by rw [hn]; exact dvd_mul_left _ _) cop E act (identity _ id) x
  have en : energy T=((p:ℤ)*2^j)^2 := hn ▸ match_excess_energy f _ _ E flat
  have same (i:ZMod p) (t u:H) : (p:ℤ)∣T (i,t)-T (i,u) := by
    simpa [T,sub_sub_sub_cancel_right,E] using horizontal_residue hf hn hs ph A i t u
  have div (x:ZMod p × H) : k-l∣T x := hn ▸ long_fibre_divisibility T ds en (pow_ne_zero _ (by decide)) hs long same x
  have hp : (0:ℤ)<p := by exact_mod_cast (Fact.out:p.Prime).pos
  have hpos : 0<k-l := by rw [hn]; exact mul_pos hp (pow_pos (by decide) _)
  obtain ⟨t,eq⟩:=integral_match_translation f _ _ hpos flat E div
  obtain ⟨z,bad⟩:=square_of_double_match hf nz cyc t eq
  have ns : ¬IsSquare (k-l) := hn ▸ nonsquare_of_valuation_one (Fact.out:p.Prime) hs
  exact ns ⟨z,by simpa [pow_two] using bad.symm⟩

theorem abelian_binary_fibre_exclusion (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (m j a b:ℕ) (k l:ℤ) (hg:Fintype.card G=p*m) (hn:k-l=(p:ℤ)*2^j)
    (check : (0 < b) ∧ (¬ (p:ℤ) ∣ (2:ℤ)^j) ∧ ((2:ZMod p) ≠ 0) ∧
      (∀ x : ZMod p, x=0 ∨ ∃ i : Fin p, (2:ZMod p)^i.val=x) ∧ (p^2 < m) ∧ p.Coprime m ∧
      IsCoprime ((2:ℤ)^j) ((p:ℤ)*m) ∧ (2^a ≡ 2 [MOD p]) ∧ (2^a ≡ 1 [MOD m]) ∧ (2^b ≡ 1 [MOD p*m])) :
    ¬∃f:G→ℤ, IsSDS k l f := by
  classical
  rcases check with ⟨bp,hs,nz,cyc,long,ph,cop,cp,ch,id⟩
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor hg ph
  have hm : Fintype.card (Additive K)=m := Nat.card_eq_fintype_card.symm.trans hK
  have total : Fintype.card (ZMod p × Additive K)=p*m := by rw [Fintype.card_prod,ZMod.card,hm]
  exact binary_fibre_exclusion (pullback hf E) j a b bp hn hs nz cyc (hm ▸ long) (hm ▸ ph)
    (by rw [total,Nat.cast_mul]; exact cop) cp (hm ▸ ch) (total ▸ id)

theorem full_binary_exclusion {k l:ℤ} {f:H→ℤ} (hf:IsSDS k l f) (nd : (2:ℤ)∣k-l)
    (odd : ¬(2:ℤ)∣(Fintype.card H:ℤ)) (kp:0<k) (klt:k<(Fintype.card H:ℤ))
    (e:ℕ) (ep:0<e) (inverse:Fintype.card H∣2^e+1) : False := by
  have acts (x:H) : 2^e • x= -x := by
    have dv : addOrderOf x∣2^e+1 := (addOrderOf_dvd_card (x:=x)).trans inverse
    have nil : (2^e+1) • x=0 := (addOrderOf_dvd_iff_nsmul_eq_zero).mp dv
    rw [add_smul,one_smul] at nil
    exact eq_neg_of_add_eq_zero_left nil
  have energyK : energy f=k := by simpa only [energy_zero,ite_true] using hf.flat 0
  obtain ⟨t,zero⟩ : ∃t:H,f t=0 := by
    by_contra! nz
    have all (x:H) : (f x)^2=1 := by rcases hf.ternary x with n|z|o <;> simp_all
    have full : energy f=(Fintype.card H:ℤ) := by simp [energy,all]
    omega
  have all (x:H) : f x=0 := by
    have ev:=self_conjugate_differences (q:=2) hf nd odd ep acts x t
    rw [zero,sub_zero] at ev
    rcases hf.ternary x with n|z|o <;> omega
  have empty : energy f=0 := by simp [energy,all]
  omega

local instance : Fact (Nat.Prime 3):=⟨by decide⟩
local instance : Fact (Nat.Prime 5):=⟨by decide⟩

theorem binary_69_52_4 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=69) :
    ¬∃f:G→ℤ, IsSDS 52 4 f := abelian_binary_fibre_exclusion (p:=3) G 23 4 11 22 52 4 hg (by decide) (by decide +kernel)
theorem binary_141_64_16 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=141) :
    ¬∃f:G→ℤ, IsSDS 64 16 f := abelian_binary_fibre_exclusion (p:=3) G 47 4 23 46 64 16 hg (by decide) (by decide +kernel)
theorem binary_141_109_61 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=141) :
    ¬∃f:G→ℤ, IsSDS 109 61 f := abelian_binary_fibre_exclusion (p:=3) G 47 4 23 46 109 61 hg (by decide) (by decide +kernel)
theorem binary_213_52_4 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=213) :
    ¬∃f:G→ℤ, IsSDS 52 4 f := abelian_binary_fibre_exclusion (p:=3) G 71 4 35 70 52 4 hg (by decide) (by decide +kernel)
theorem binary_155_99_19 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=155) :
    ¬∃f:G→ℤ, IsSDS 99 19 f := abelian_binary_fibre_exclusion (p:=5) G 31 4 5 20 99 19 hg (by decide) (by decide +kernel)

theorem binary_177_49_1 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=177) :
    ¬∃f:G→ℤ, IsSDS 49 1 f := by
  rintro ⟨f,hf⟩
  exact full_binary_exclusion hf (by decide) (by rw [hg]; decide) (by decide) (by rw [hg]; decide)
    29 (by decide) (by rw [hg]; decide)
theorem binary_393_49_1 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=393) :
    ¬∃f:G→ℤ, IsSDS 49 1 f := by
  rintro ⟨f,hf⟩
  exact full_binary_exclusion hf (by decide) (by rw [hg]; decide) (by decide) (by rw [hg]; decide)
    65 (by decide) (by rw [hg]; decide)

#print axioms abelian_binary_fibre_exclusion
#print axioms binary_155_99_19
#print axioms binary_393_49_1

end Signed39.Contraction
