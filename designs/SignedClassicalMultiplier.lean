import SignedMixedVariance
import SignedSelfConjugacy

/-! An elementary version of the classical squarefree multiplier test at a prime quotient. -/

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [AddCommGroup H] [DecidableEq H] in
theorem equiv_mass (e : H ≃ H) (u : H → ℤ) : mass (fun x=>u (e x))=mass u :=
  Fintype.sum_equiv e _ _ (fun _ => rfl)

omit [DecidableEq H] in
theorem centered_match (u v : H → ℤ) (t : H) :
    matched (fun x=>(Fintype.card H:ℤ)*u x-mass u)
      (fun x=>(Fintype.card H:ℤ)*v x-mass v) t=
    (Fintype.card H:ℤ)^2*matched u v t-(Fintype.card H:ℤ)*mass u*mass v := by
  let m : ℤ := Fintype.card H
  have sv : (∑ x, v (x-t))=mass v := by simpa only [sub_eq_add_neg,mass] using sum_translate v (-t)
  calc
    _=∑ x, (m^2*(u x*v (x-t))-(m*mass v)*u x-(m*mass u)*v (x-t)+mass u*mass v) := by
      apply sum_congr rfl; intro x _; dsimp only [m]; ring
    _=_ := by simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,sv,sum_const,card_univ,nsmul_eq_mul]
              change m^2*matched u v t-(m*mass v)*mass u-(m*mass u)*mass v+mass u*(m*mass v)=_
              ring

variable {q : ℕ} [Fact q.Prime]

theorem frobenius_match_zero (u : H → ℤ) (e : H ≃+ H) (k : ℕ) (scalar : ∀x:H, q^k • x=e x)
    (zero : ∀t, (q:ℤ)∣corr u t) (t : H) : (q:ℤ)∣matched (fun x=>u (e.symm x)) u t := by
  let g := fun x:H => (u x:ZMod q)
  have fg : forward g*backward g=0 := by
    apply AddMonoidAlgebra.ext; ext t
    rw [cross_coeff]
    simpa [g,corr,add_comm,mul_comm] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (zero t)
  have ep : forward (fun x=>g (e.symm x))=(forward g)^(q^k) := by
    rw [frobenius_forward]
    simp only [scalar,forward]
    exact Fintype.sum_equiv e.symm.toEquiv _ _ (fun x=>by simp)
  have positive := pow_pos (Fact.out : q.Prime).pos k
  have nil : forward (fun x=>g (e.symm x))*backward g=0 := by
    rw [ep,show q^k=q^k-1+1 by omega,pow_succ,mul_assoc,fg,mul_zero]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  have eq := congrArg (fun a:AddMonoidAlgebra (ZMod q) H => a.coeff t) nil
  rw [cross_coeff] at eq
  simpa [matched_shift,g] using eq

theorem prime_multiplier_dvd (u : H → ℤ) (n l : ℤ) (flat : ∀ t, corr u t=(if t=0 then n else 0)+l)
    (qn : (q:ℤ)∣n) (qm : ¬(q:ℤ)∣(Fintype.card H:ℤ)) (e : H ≃+ H) (k : ℕ)
    (scalar : ∀ x:H, q^k • x=e x) (t : H) :
    (q:ℤ)∣matched (fun x=>u (e.symm x)) u t-l := by
  let m : ℤ := Fintype.card H
  let b := fun x=>m*u x-mass u
  let a := fun x=>u (e.symm x)
  have sq := mass_from_flat u n l flat
  change (mass u)^2=n+m*l at sq
  have ca (v : H → ℤ) (t : H) : corr v t=matched v v (-t) := by simp [corr,matched]
  have bz (t : H) : (q:ℤ)∣corr b t := by
    rw [ca]; dsimp only [b,m]; rw [centered_match,← ca,flat]
    by_cases t0 : t=0
    · simp only [t0,ite_true]
      obtain ⟨w,hw⟩ := qn
      refine ⟨(m^2-m)*w,?_⟩
      change m^2*(n+l)-m*mass u*mass u=_
      linear_combination -m*sq+(m^2-m)*hw
    · simp only [ite_eq_right t0,zero_add]
      obtain ⟨w,hw⟩ := qn
      refine ⟨-m*w,?_⟩
      change m^2*l-m*mass u*mass u=_
      linear_combination -m*sq-m*hw
  have c := frobenius_match_zero b e k scalar bz t
  have eq : (fun x=>b (e.symm x))=fun x=>m*a x-mass a := by
    have h := equiv_mass e.symm.toEquiv u
    change mass a=mass u at h
    simp only [h,a,b]
  rw [eq] at c
  change (q:ℤ)∣matched (fun x=>m*a x-mass a) (fun x=>m*u x-mass u) t at c
  rw [centered_match] at c
  have ma : mass a=mass u := equiv_mass e.symm.toEquiv u
  rw [ma] at c
  obtain ⟨w,hw⟩ := c
  obtain ⟨z,hz⟩ := qn
  have lifted : (q:ℤ)∣m^2*(matched a u t-l) := by
    refine ⟨w+m*z,?_⟩
    change m^2*matched a u t-m*mass u*mass u=(q:ℤ)*w at hw
    linear_combination hw+m*sq+m*hz
  have prime := Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)
  exact (prime.dvd_or_dvd lifted).resolve_left (fun d=>qm (prime.dvd_of_dvd_pow d))

theorem integral_match_translation (u : H → ℤ) (n l : ℤ) (positive : 0<n)
    (flat : ∀ t, corr u t=(if t=0 then n else 0)+l)
    (e : H ≃+ H) (dv : ∀t, n∣matched (fun x=>u (e.symm x)) u t-l) :
    ∃ t : H, ∀ x : H, u (e.symm x)=u (x-t) := by
  let a := fun x=>u (e.symm x)
  let h := matched a u
  let m : ℤ := Fintype.card H
  have mh : 0 < m := by dsimp [m]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H)
  have ma : mass a=mass u := equiv_mass e.symm.toEquiv u
  have ea : energy a=energy u := Fintype.sum_equiv e.symm.toEquiv _ _ (fun _ => rfl)
  have sq := mass_from_flat u n l flat
  change (mass u)^2=n+m*l at sq
  have eu : energy u=n+l := by simpa [←energy_zero] using flat 0
  choose z hz using dv
  have expr : h=fun t =>l+n*z t := funext (fun t=>by have t0:=hz t; dsimp [h,a]; omega)
  have hm : mass h=m*l+n*mass z := calc
    _=mass (fun t=>l+n*z t) := congrArg mass expr
    _=_ := by simp [mass,sum_add_distrib,←mul_sum,m]
  have mass1 : mass z=1 := by
    have h' := matched_mass a u
    change mass h=mass a*mass u at h'
    rw [ma,hm] at h'
    apply mul_left_cancel₀ positive.ne'
    linear_combination h'+sq
  have vu : variance a=(m-1)*n := by rw [variance,ea,ma,eu,sq]; change m*(n+l)-(n+m*l)=(m-1)*n; ring
  have ve := matched_variance a u n l flat
  change variance h=n*variance a at ve
  rw [expr,variance_affine,vu] at ve
  have vz : variance z=m-1 := by apply mul_left_cancel₀ (pow_ne_zero 2 positive.ne'); linear_combination ve
  have ez : energy z=1 := by
    rw [variance,mass1] at vz
    apply mul_left_cancel₀ mh.ne'
    linear_combination vz
  obtain ⟨t',one⟩ : ∃ t, z t=1 := by
    by_contra! all
    have neg (t : H) : z t≤0 := by
      have bound : (z t)^2≤1 := ez ▸ single_le_sum (fun _ _=>sq_nonneg _) (mem_univ t)
      by_contra! h
      have two : 2≤z t := by have := all t; omega
      nlinarith [mul_nonneg (show 0≤z t-2 by omega) (show 0≤z t+2 by omega)]
    have h := sum_nonpos (s:=univ) (fun t _=>neg t)
    change mass z≤0 at h
    omega
  have atT : matched a u t'=n+l := by have he:=congrFun expr t'; change h t'=l+n*z t' at he; simpa [h,one,add_comm] using he
  have es : (∑ x, (u (x-t'))^2)=energy u := by
    simpa [sub_eq_add_neg,energy] using sum_translate (fun x=>(u x)^2) (-t')
  have zero : (∑ x, (a x-u (x-t'))^2)=0 := calc
    _=∑ x, ((a x)^2+(u (x-t'))^2-2*(a x*u (x-t'))) := by apply sum_congr rfl; intro x _; ring
    _=_ := by
      simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,es]
      change energy a+energy u-2*matched a u t'=0
      rw [ea,eu,atT]; ring
  refine ⟨t',fun x=>?_⟩
  have ax := (sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (a x-u (x-t')))).mp zero x (mem_univ x)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ax)

#print axioms prime_multiplier_dvd
#print axioms integral_match_translation

end Signed39.Contraction
