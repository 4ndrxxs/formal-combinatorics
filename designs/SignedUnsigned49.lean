import SignedAlmostBinary
import SignedFibreFactorization

namespace Signed39.Contraction

open Finset

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {H:Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

private theorem fixed_unsigned {D:H→ℤ} (hm:Fintype.card H=49) (bin:∀x,D x=0∨D x=1)
    (ms:mass D=16) (flat:∀z,corr D z=(if z=0 then 11 else 0)+5) :
    ∃f:H→ℤ,(∀x,f x=0∨f x=1) ∧ mass f=16 ∧ (∀x,f (11 • x)=f x) ∧
      ∀z,corr f z=(if z=0 then 11 else 0)+5 := by
  let E:=scalarPerm (H:=H) 11 9 (hm ▸ (by decide))
  have all (x:H) : (11:ℤ)∣matched (fun y=>D (E.symm y)) D x-5 :=
    aux_dvd D 49 11 11 5 flat E hm (fun _=>rfl) ⟨11,1,1,21⟩ (by decide) x
  obtain ⟨g,tr⟩:=integral_match_translation D 11 5 (by decide) flat E all
  let base:=5 • g
  let f:=fun x=>D (x+base)
  have val: 11 • base-base=g := by
    change 11 • (5 • g)-5 • g=g
    rw [←mul_nsmul]
    have eq : (55:ℕ) • g=6 • g := scalar_congr (hm ▸ (by decide)) g
    rw [eq,show (6:ℕ) • g=5 • g+g by rw [show (6:ℕ)=5+1 by decide,add_nsmul,one_nsmul]]
    abel
  refine ⟨f,fun x=>bin _,(sum_translate D base).trans ms,fun x=>?_,fun z=>?_⟩
  · have row:=tr (E (x+base))
    rw [E.symm_apply_apply] at row
    have add:11 • base-g=base:=by rw [←val]; abel
    change D (x+base)=D (11 • (x+base)-g) at row
    rw [nsmul_add,add_sub_assoc,add] at row
    exact row.symm
  · have eq:corr f z=corr D z:=by
      unfold corr
      exact Fintype.sum_equiv (Equiv.addRight base) _ _ (fun x=>by dsimp [f]; rw [show x+z+base=x+base+z by abel])
    exact eq.trans (flat z)

private theorem torsion_seven {D:H→ℤ} (hm:Fintype.card H=49) (bin:∀x,D x=0∨D x=1)
    (ms:mass D=16) (fix:∀x,D (11 • x)=D x) (flat:∀z,corr D z=(if z=0 then 11 else 0)+5) :
    ∀x:H,7 • x=0 := by
  have killed (x:H) (bad:7 • x≠0) : D x=0 := by
    have dv:=addOrderOf_dvd_card (x:=x)
    rw [hm] at dv
    have le:=Nat.le_of_dvd (by decide : 0<49) dv
    have raw : ∀i:Fin 50,i.val∣49 → i.val∣7 ∨ i.val=49 := by decide
    have exactly:addOrderOf x=49 := (raw ⟨addOrderOf x,Nat.lt_succ_of_le le⟩ dv).resolve_left (fun h=>bad (addOrderOf_dvd_iff_nsmul_eq_zero.mp h))
    let orbit:Fin 21→H:=fun j=>11^j.val • x
    have inject:Function.Injective orbit := by
      intro i j eq
      have md:=nsmul_eq_nsmul_iff_modEq.mp eq
      rw [exactly] at md
      have good:∀i j:Fin 21,11^i.val≡11^j.val [MOD 49] → i=j := by decide +kernel
      exact good i j md
    have fp (j:ℕ) : D (11^j • x)=D x := by
      induction j with
      | zero=>simp
      | succ j ih=>rw [pow_succ,show (11^j*11) • x=11 • (11^j • x) by rw [←mul_nsmul],fix,ih]
    rcases bin x with ez|eo
    · exact ez
    · have sum:(∑y∈univ.image orbit,D y)=21 := by
        rw [sum_image (fun i _ j _ e=>inject e)]
        simp only [orbit,fp,eo,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
        rfl
      have le:=sum_le_sum_of_subset_of_nonneg (subset_univ (univ.image orbit)) (f:=D) (fun y _ _=>by rcases bin y with h|h <;> omega)
      change _ ≤ mass D at le
      rw [sum,ms] at le; omega
  intro t
  by_contra bad
  have nz:t≠0:=by intro h; simp [h] at bad
  have no (x:H) : D x*D (x+t)=0 := by
    by_cases hx:7 • x=0
    · have neq:7 • (x+t)≠0:=by rwa [nsmul_add,hx,zero_add]
      rw [killed _ neq,mul_zero]
    · rw [killed _ hx,zero_mul]
  have e:=flat t
  simp [corr,no,nz] at e


private theorem line_arithmetic (a b c:ℤ) (ha:0≤a) (hb:0≤b) (hc:0≤c)
    (m:a+3*b+3*c=16) (e:a^2+3*b^2+3*c^2=46) : a=4 := by
  have bl:b≤3:=by nlinarith [sq_nonneg a,sq_nonneg c,sq_nonneg (b-4)]
  have cl:c≤3:=by nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg (c-4)]
  interval_cases b <;> interval_cases c <;> simp_all <;> nlinarith

private theorem central_mass {D:H→ℤ} (hm:Fintype.card H=49) (bin:∀x,D x=0∨D x=1)
    (ms:mass D=16) (fix:∀x,D (11 • x)=D x) (flat:∀z,corr D z=(if z=0 then 11 else 0)+5)
    (φ:H→+ZMod 7) (surj:Function.Surjective φ) : projected φ D 0=4 := by
  let U:=projected φ D
  let T:=scalarPerm (H:=H) 11 9 (hm ▸ (by decide))
  have ker:=AddSubgroup.card_ker_mul_card_of_surjective surj
  rw [Nat.card_eq_fintype_card (α:=H),hm,Nat.card_eq_fintype_card (α:=ZMod 7),ZMod.card] at ker
  have ck:Nat.card φ.ker=7:=by omega
  have hD:IsSDS 16 5 D := ⟨fun x=>by rcases bin x with h|h <;> simp [h],fun x=>by rw [flat]; split <;> decide⟩
  have energy7:energy U=46 := by
    rw [energy_zero,projected_flat φ surj hD,ck]; norm_num
  have mu:mass U=16 := by change (∑i:ZMod 7,∑x:H,if φ x=i then D x else 0)=16; rw [sum_comm]; simpa [mass] using ms
  have non (i:ZMod 7) : 0≤U i := sum_nonneg (fun x _=>by split <;> rcases bin x with h|h <;> omega)
  have op (i:ZMod 7) : U (4*i)=U i := by
    symm
    change (∑x:H,if φ x=i then D x else 0)=(∑x:H,if φ x=4*i then D x else 0)
    apply Fintype.sum_equiv T.toEquiv
    intro x
    change (if φ x=i then D x else 0)=(if φ (11 • x)=4*i then D (11 • x) else 0)
    rw [map_nsmul,nsmul_eq_mul,show ((11:ℕ):ZMod 7)=4 by decide,fix]
    simp only [mul_right_inj' (by decide : (4:ZMod 7)≠0)]
  have h4:U 4=U 1:=by simpa only [show (4:ZMod 7)*1=4 by decide] using op 1
  have h2:U 2=U 1:=by simpa only [show (4:ZMod 7)*4=2 by decide,h4] using op 4
  have h5:U 5=U 3:=by simpa only [show (4:ZMod 7)*3=5 by decide] using op 3
  have h6:U 6=U 3:=by simpa only [show (4:ZMod 7)*5=6 by decide,h5] using op 5
  have sums (g:ℤ→ℤ) : (∑i:ZMod 7,g (U i))=g (U 0)+3*g (U 1)+3*g (U 3) := by
    change (∑i:Fin 7,g (U i))=_
    simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty]
    change g (U 0)+(g (U 1)+(g (U 2)+(g (U 3)+(g (U 4)+(g (U 5)+(g (U 6)+0))))))=_
    rw [h2,h4,h5,h6]; ring
  apply line_arithmetic (U 0) (U 1) (U 3) (non _) (non _) (non _)
  · exact (sums id).symm.trans mu
  · exact (sums (fun z=>z^2)).symm.trans energy7

private theorem line_mass {D:H→ℤ} (hm:Fintype.card H=49) (bin:∀x,D x=0∨D x=1)
    (ms:mass D=16) (fix:∀x,D (11 • x)=D x) (flat:∀z,corr D z=(if z=0 then 11 else 0)+5)
    (h:H) (nz:h≠0) (kill:7 • h=0) : (∑j:Fin 7,D (j.val • h))=4 := by
  classical
  have dv:=addOrderOf_dvd_iff_nsmul_eq_zero.mpr kill
  have order:addOrderOf h=7 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp dv with e|e
    · have z:1 • h=0:=addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [e]); rw [one_nsmul] at z; contradiction
    · exact e
  let L:=AddSubgroup.zmultiples h
  have size:Nat.card L=7:=(Nat.card_zmultiples h).trans order
  have cq:=AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup L
  rw [Nat.card_eq_fintype_card (α:=H),hm,size] at cq
  let : Fintype (H⧸L):=Fintype.ofFinite _
  have rq:Fintype.card (H⧸L)=7 := by rw [←Nat.card_eq_fintype_card]; omega
  obtain ⟨γ,onto⟩:=exists_prime_quotient (G:=H⧸L) 7 (by decide) (by rw [rq])
  let π:=γ.comp (QuotientAddGroup.mk' L)
  have sur:Function.Surjective π:=onto.comp (QuotientAddGroup.mk'_surjective L)
  have ker:=AddSubgroup.card_ker_mul_card_of_surjective sur
  rw [Nat.card_eq_fintype_card (α:=H),hm,Nat.card_eq_fintype_card (α:=ZMod 7),ZMod.card] at ker
  have Hcard:Fintype.card π.ker=7:=by rw [←Nat.card_eq_fintype_card]; omega
  have ph:π h=0 := by
    have mem:h∈(QuotientAddGroup.mk' L).ker:=by rw [QuotientAddGroup.ker_mk']; exact AddSubgroup.mem_zmultiples h
    change γ ((QuotientAddGroup.mk' L) h)=0; rw [show (QuotientAddGroup.mk' L) h=0 from mem,map_zero]
  let z:Fin 7→π.ker:=fun i=>⟨i.val • h,by change π (i.val • h)=0; rw [map_nsmul,ph,nsmul_zero]⟩
  have inj:Function.Injective z := by
    intro a b eq
    have mod:=nsmul_eq_nsmul_iff_modEq.mp (show a.val • h=b.val • h from congrArg Subtype.val eq)
    rw [order] at mod
    exact Fin.ext (by simpa [Nat.ModEq,Nat.mod_eq_of_lt a.isLt,Nat.mod_eq_of_lt b.isLt] using mod)
  let e:=Equiv.ofBijective z ((Fintype.bijective_iff_injective_and_card z).mpr ⟨inj,by rw [Fintype.card_fin,Hcard]⟩)
  have sum:(∑i:Fin 7,D (i.val • h))=∑x:π.ker,D x:=Fintype.sum_equiv e _ _ (fun _=>rfl)
  have image:projected π D 0=∑x:π.ker,D x := by
    change (∑x:H,if π x=0 then D x else 0)=_
    rw [←sum_filter]
    exact sum_subtype _ (fun x=>by simp) D
  exact sum.trans (image.symm.trans (central_mass hm bin ms fix flat π sur))

theorem no_unsigned_49 (hm:Fintype.card H=49) (D:H→ℤ) (bin:∀x,D x=0∨D x=1)
    (ms:mass D=16) (flat:∀z,corr D z=(if z=0 then 11 else 0)+5) : False := by
  obtain ⟨f,bit,mf,fix,flatF⟩:=fixed_unsigned hm bin ms flat
  have all:=torsion_seven hm bit mf fix flatF
  have line (h:H) : (∑j:Fin 7,f (j.val • h))=(if h=0 then 7*f 0 else 4) := by
    by_cases z:h=0
    · simp [z]
    · rw [if_neg z]; exact line_mass hm bit mf fix flatF h z (all h)
  have perm (j:Fin 7) (nz:j.val≠0) : (∑h:H,f (j.val • h))=16 := by
    have existsInv:∀a:Fin 7,a.val≠0 → ∃b:Fin 7,a.val*b.val≡1 [MOD 7] := by decide
    obtain ⟨k,inv⟩:=existsInv j nz
    have cancel (h:H) : (j.val*k.val) • h=h :=
      (nsmul_eq_nsmul_iff_modEq.mpr (inv.of_dvd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr (all h)))).trans (one_nsmul h)
    let E : H ≃ H := {
      toFun := fun h=>j.val • h
      invFun := fun h=>k.val • h
      left_inv := fun h=>by change k.val • (j.val • h)=h; rw [←mul_nsmul]; exact cancel h
      right_inv := fun h=>by change j.val • (k.val • h)=h; rw [←mul_nsmul,Nat.mul_comm]; exact cancel h }
    exact (Fintype.sum_equiv E _ _ (fun _=>rfl)).trans mf
  have value (j:Fin 7) : (∑h:H,f (j.val • h))=if j=0 then 49*f 0 else 16 := by
    by_cases z:j=0
    · simp [z,hm]
    · rw [if_neg z]; exact perm j (fun e=>z (Fin.ext e))
  have total:(∑h:H,∑j:Fin 7,f (j.val • h))=∑j:Fin 7,∑h:H,f (j.val • h):=sum_comm
  have lhs (h:H) : (if h=0 then 7*f 0 else 4)=(if h=0 then 7*f 0-4 else 0)+4 := by split <;> omega
  have rhs (j:Fin 7) : (if j=0 then 49*f 0 else 16)=(if j=0 then 49*f 0-16 else 0)+16 := by split <;> omega
  simp only [line,value,lhs,rhs,sum_add_distrib,sum_ite_eq',mem_univ,ite_true,sum_const,card_univ,hm,Fintype.card_fin,nsmul_eq_mul] at total
  omega

#print axioms no_unsigned_49


end Signed39.Contraction
