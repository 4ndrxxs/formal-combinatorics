import SignedBinaryMultiplier

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
variable {p : ℕ} [Fact p.Prime]

theorem match_excess_energy (f : H → ℤ) (n l : ℤ) (E : H ≃+ H)
    (flat : ∀t,corr f t=(if t=0 then n else 0)+l) :
    energy (fun t=>matched (fun x=>f (E.symm x)) f t-l)=n^2 := by
  let v:ℤ:=Fintype.card H
  let d:=fun x=>f (E.symm x)
  let h:=matched d f
  let T:=fun t=>h t-l
  have hv : v≠0 := by dsimp [v]; exact_mod_cast (Fintype.card_ne_zero : Fintype.card H≠0)
  have md : mass d=mass f := equiv_mass E.symm.toEquiv f
  have ed : energy d=energy f := Fintype.sum_equiv E.symm.toEquiv _ _ (fun _=>rfl)
  have sq:=mass_from_flat f n l flat
  change (mass f)^2=n+v*l at sq
  have ef : energy f=n+l := by simpa [←energy_zero] using flat 0
  have vd : variance d=(v-1)*n := by
    rw [variance,md,ed,ef,sq]; change v*(n+l)-(n+v*l)=(v-1)*n; ring
  have mh : mass h=(mass f)^2 := by rw [show mass h=mass d*mass f from matched_mass _ _,md,pow_two]
  have mt : mass T=n := by
    have eq : mass T=mass h-v*l := by simp [T,mass,v,sum_sub_distrib]
    rw [eq,mh,sq]; ring
  have vt : variance T=variance h := by
    simpa only [T,one_mul,one_pow,sub_eq_neg_add] using variance_affine h (-l) 1
  have vh:=matched_variance d f n l flat
  change variance h=n*variance d at vh
  rw [vd] at vh
  rw [variance,mt] at vt
  change v*energy T-n^2=variance h at vt
  apply mul_left_cancel₀ hv
  change v*energy T=v*n^2
  linear_combination vt+vh

theorem horizontal_residue {k l s : ℤ} {f : ZMod p × H → ℤ} (hf : IsSDS k l f)
    (hn : k-l=(p:ℤ)*s) (hs : ¬(p:ℤ)∣s) (hc : p.Coprime (Fintype.card H))
    (A : ZMod p ≃+ ZMod p) (i : ZMod p) (t u : H) :
    let E:=A.prodCongr (AddEquiv.refl H)
    (p:ℤ)∣matched (fun x=>f (E.symm x)) f (i,t)-matched (fun x=>f (E.symm x)) f (i,u) := by
  let E:=A.prodCongr (AddEquiv.refl H)
  have expand (t:H) : matched (fun x=>f (E.symm x)) f (i,t)=
      ∑j:ZMod p,cross (row f j) (row f (A.symm (i+j))) t := by
    rw [matched_shift,Fintype.sum_prod_type]
    apply sum_congr rfl; intro j _
    apply sum_congr rfl; intro x _
    change f (A.symm (i+j),t+x)*f (j,x)=f (j,x)*f (A.symm (i+j),x+t)
    rw [add_comm t x,mul_comm]
  change (p:ℤ)∣matched (fun x=>f (E.symm x)) f (i,t)-matched (fun x=>f (E.symm x)) f (i,u)
  rw [expand,expand,←sum_sub_distrib]
  apply dvd_sum; intro j _
  let w:=A.symm (i+j)
  have h:=dvd_sub (row_cross_dvd hf hn hc j w t) (row_cross_dvd hf hn hc j w u)
  have ds : (p:ℤ)∣s*(cross (row f j) (row f w) t-cross (row f j) (row f w) u) := by convert h using 1; ring
  exact ((Nat.prime_iff_prime_int.mp (Fact.out:p.Prime)).dvd_or_dvd ds).resolve_left hs

omit [AddCommGroup H] [DecidableEq H] in
theorem long_fibre_divisibility {s : ℤ} (T : ZMod p × H → ℤ) (ds : ∀x,s∣T x)
    (en : energy T=((p:ℤ)*s)^2) (sz : s≠0) (hs : ¬(p:ℤ)∣s) (long : p^2<Fintype.card H)
    (same : ∀(i:ZMod p)(t u:H),(p:ℤ)∣T (i,t)-T (i,u)) :
    ∀x,(p:ℤ)*s∣T x := by
  choose z hz using ds
  have ez : energy z=(p:ℤ)^2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 sz)
    calc
      s^2*energy z=energy T := by simp only [energy,mul_sum,hz,mul_pow]
      _=s^2*(p:ℤ)^2 := by rw [en]; ring
  intro x
  have dp : (p:ℤ)∣T x := by
    by_contra bad
    have non (t:H) : z (x.1,t)≠0 := by
      intro zero
      have h:=same x.1 x.2 t
      change (p:ℤ)∣T x-T (x.1,t) at h
      rw [hz (x.1,t),zero,mul_zero,sub_zero] at h
      exact bad h
    have low (t:H) : (1:ℤ)≤(z (x.1,t))^2 := by have h:=sq_pos_of_ne_zero (non t); omega
    have slice := sum_le_sum (s:=univ) (fun t _=>low t)
    simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at slice
    have whole : (∑t:H,(z (x.1,t))^2)≤energy z := by
      change _≤∑u,(z u)^2
      rw [Fintype.sum_prod_type]
      exact single_le_sum (fun j _=>sum_nonneg (fun t _=>sq_nonneg (z (j,t)))) (mem_univ x.1)
    rw [ez] at whole
    exact (not_le_of_gt (by exact_mod_cast long : (p:ℤ)^2 < (Fintype.card H:ℤ))) (slice.trans whole)
  rw [hz] at dp
  obtain ⟨a,ha⟩:=((Nat.prime_iff_prime_int.mp (Fact.out:p.Prime)).dvd_or_dvd dp).resolve_left hs
  exact ⟨a,by rw [hz,ha]; ring⟩

#print axioms long_fibre_divisibility

end Signed39.Contraction
