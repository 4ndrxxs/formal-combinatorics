import SignedLongSigns
import SignedFibreSum

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
theorem scalar_congr {a b:ℕ} (eq:a ≡ b [MOD Fintype.card H]) (x:H) : a • x=b • x :=
  nsmul_eq_nsmul_iff_modEq.mpr (eq.of_dvd (addOrderOf_dvd_card (x:=x)))

omit [DecidableEq H] in
def scalarPerm (t inv:ℕ) (hi:t*inv ≡ 1 [MOD Fintype.card H]) : H≃+H where
  toFun x:=t • x
  invFun x:=inv • x
  left_inv x:=by change inv • (t • x)=x; rw [←mul_nsmul,scalar_congr hi,one_nsmul]
  right_inv x:=by change t • (inv • x)=x; rw [←mul_nsmul,Nat.mul_comm,scalar_congr hi,one_nsmul]
  map_add' x y:=nsmul_add _ _ _

structure AuxPower where
  q : ℕ
  j : ℕ
  a : ℕ
  b : ℕ
  deriving Repr,DecidableEq

def powerConditions (v t n:ℕ) (z:AuxPower) : Prop :=
  z.q.Prime ∧ 0<z.b ∧ z.q^z.a ≡ t [MOD v] ∧ z.q^z.b ≡ 1 [MOD v] ∧
    IsCoprime ((z.q:ℤ)^z.j) (v:ℤ) ∧ (z.q:ℤ)^z.j∣(n:ℤ)
instance (v t n:ℕ) (z:AuxPower) : Decidable (powerConditions v t n z) := by unfold powerConditions; infer_instance

theorem aux_dvd {G:Type} [AddCommGroup G] [Fintype G] [DecidableEq G] (f:G→ℤ) (v t n:ℕ) (l:ℤ)
    (flat:∀x,corr f x=(if x=0 then (n:ℤ) else 0)+l) (E:G≃+G) (hg:Fintype.card G=v)
    (act:∀x:G,t • x=E x) (z:AuxPower) (ok:powerConditions v t n z) (x:G) :
    (z.q:ℤ)^z.j∣matched (fun y=>f (E.symm y)) f x-l := by
  obtain ⟨qp,bp,fa,idc,co,div⟩:=ok
  let : Fact z.q.Prime:=⟨qp⟩
  exact prime_power_multiplier_dvd f n l flat z.j z.a z.b bp div (hg ▸ co) E
    (fun y=>(scalar_congr (hg ▸ fa) y).trans (act y)) (fun y=>(scalar_congr (hg ▸ idc) y).trans (one_nsmul y)) x

def longHeader (p m s t inv step r _d : ℕ) (k l M:ℤ) (u v:AuxPower) : Prop :=
  0 < m ∧ p.Coprime m ∧ ¬(p:ℤ)∣(s:ℤ) ∧ 0<s ∧ 0<t ∧ k-l=(p:ℤ)*s ∧
  M^2=k-l+(p:ℤ)*m*l ∧ t ≡ 1 [MOD p] ∧ p^r ≡ t [MOD m] ∧
  t*inv ≡ 1 [MOD m] ∧ (t-1)*step ≡ 1 [MOD m] ∧
  powerConditions (p*m) t (p*s) u ∧ powerConditions (p*m) t (p*s) v ∧
  (u.q:ℤ)^u.j*(v.q:ℤ)^v.j=(s:ℤ) ∧ IsCoprime ((u.q:ℤ)^u.j) ((v.q:ℤ)^v.j)

instance (p m s t inv step r d : ℕ) (k l M:ℤ) (u v:AuxPower) :
    Decidable (longHeader p m s t inv step r d k l M u v) := by unfold longHeader; infer_instance

def missesSigns (p d:ℕ) (k M:ℤ) : Prop := ∀a b:Fin (p+1),a.val+b.val≤p →
  ¬((d:ℤ)∣(k+M)/2-a.val ∧ (d:ℤ)∣(k-M)/2-b.val)

instance (p d:ℕ) (k M:ℤ) : Decidable (missesSigns p d k M) := by unfold missesSigns; infer_instance

theorem long_fixed_word (p m s t inv step r d : ℕ) [Fact p.Prime] (k l M:ℤ) (u v:AuxPower)
    (hm:Fintype.card H=m) (header:longHeader p m s t inv step r d k l M u v)
    (f:ZMod p×H→ℤ) (hf:IsSDS k l f) :
    ∃base:H,∀i x,f (i,t • x+base)=f (i,x+base) := by
  obtain ⟨_,cop,nodiv,pos,tp,hn,sq,first,rest,vinv,aff,uc,vc,sz,dis⟩:=header
  let B:=scalarPerm (H:=H) t inv (hm ▸ vinv)
  let E:=(AddEquiv.refl (ZMod p)).prodCongr B
  have total : Fintype.card (ZMod p×H)=p*m := by rw [Fintype.card_prod,ZMod.card,hm]
  have action (x:ZMod p×H) : t • x=E x := by
    apply Prod.ext
    · change t • x.1=x.1
      exact (scalar_congr (by rwa [ZMod.card]) x.1).trans (one_nsmul _)
    · rfl
  have flat (x:ZMod p×H) : corr f x=(if x=0 then ((p*s:ℕ):ℤ) else 0)+l := by
    rw [hf.flat]; push_cast; split <;> omega
  have ds (x:ZMod p×H) : (s:ℤ)∣matched (fun y=>f (E.symm y)) f x-l := sz ▸ dis.mul_dvd
    (aux_dvd f _ _ _ _ flat E total action u uc x) (aux_dvd f _ _ _ _ flat E total action v vc x)
  have sm : (0:ℤ)<s := by exact_mod_cast pos
  have matchEq:=fixed_quotient_multiplier hf hn nodiv sm (hm ▸ cop) B r
    (fun x=>scalar_congr (hm ▸ rest) x) ds
  have surj (y:H) : ∃b,B b-b=y := by
    refine ⟨step • y,?_⟩
    change t • (step • y)-step • y=y
    have e : (t-1) • (step • y)+step • y=t • (step • y) := by
      simpa only [add_nsmul,one_nsmul] using congrArg (fun n:ℕ=>n • (step • y)) (show t-1+1=t by omega)
    rw [←e,add_sub_cancel_right,←mul_nsmul,Nat.mul_comm,scalar_congr (hm ▸ aff),one_nsmul]
  have hp : (0:ℤ)<p := by exact_mod_cast (Fact.out:p.Prime).pos
  exact row_multiplier_fixed hf (hn ▸ mul_pos hp sm) B surj matchEq

theorem long_sign_exclusion (p m s t inv step r d : ℕ) [Fact p.Prime] (k l M:ℤ) (u v:AuxPower)
    (hm:Fintype.card H=m) (W:H→ℤ) (levels:∀x:H,(d:ℤ)∣(if x=0 then (0:ℤ) else 1)+W (t • x)-W x)
    (header:longHeader p m s t inv step r d k l M u v) (bad:missesSigns p d k M) :
    ¬∃f:ZMod p×H→ℤ,IsSDS k l f := by
  rintro ⟨f,hf⟩
  have md:=sds_mass hf
  have sq:=header.2.2.2.2.2.2.1
  rw [Fintype.card_prod,ZMod.card,hm,Nat.cast_mul,←sq] at md
  obtain ⟨g,hg,ms⟩ : ∃g:ZMod p×H→ℤ,IsSDS k l g ∧ mass g=M := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp md with pos|neg
    · exact ⟨f,hf,pos⟩
    · exact ⟨fun x=> -f x,hf.neg,by simpa only [mass,sum_neg_distrib,neg_eq_iff_eq_neg] using neg⟩
  obtain ⟨base,fix⟩:=long_fixed_word p m s t inv step r d k l M u v hm header g hg
  let B:=scalarPerm (H:=H) t inv (hm ▸ header.2.2.2.2.2.2.2.2.2.1)
  obtain ⟨a,b,cap,pos,neg⟩:=fixed_sign_counts hg B base fix d W levels
  rw [ms] at pos neg
  exact (bad a b cap) ⟨pos,neg⟩

#print axioms long_sign_exclusion

end Signed39.Contraction

