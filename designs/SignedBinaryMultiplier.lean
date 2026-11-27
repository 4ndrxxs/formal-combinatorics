import SignedFrobeniusLift
import SignedClassicalMultiplier
import Mathlib.Algebra.MonoidAlgebra.MapDomain

namespace Signed39.Contraction

open Finset

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in
private theorem scalar_coeff (n : ℤ) (A : AddMonoidAlgebra ℤ H) (i : H) :
    ((n:AddMonoidAlgebra ℤ H)*A).coeff i=n*A.coeff i := by
  rw [AddMonoidAlgebra.intCast_def,AddMonoidAlgebra.coeff_single_zero_mul]; simp

private theorem scalar_dvd (n : ℤ) (A : AddMonoidAlgebra ℤ H) :
    (n:AddMonoidAlgebra ℤ H)∣A ↔ ∀i,n∣A.coeff i := by
  constructor
  · rintro ⟨B,rfl⟩ i
    exact ⟨B.coeff i,scalar_coeff n B i⟩
  · intro h
    choose z hz using h
    refine ⟨forward z,?_⟩
    apply AddMonoidAlgebra.ext; ext i
    rw [scalar_coeff,forward_coeff,hz]

omit [DecidableEq H] in
private theorem binary_action (E : H ≃+ H) (u : H → ℤ) :
    AddMonoidAlgebra.mapDomainRingHom ℤ E.toAddMonoidHom (forward u)=forward (fun x=>u (E.symm x)) := by
  simp only [forward,map_sum,AddMonoidAlgebra.mapDomainRingHom_apply,AddMonoidAlgebra.mapDomain_single]
  exact Fintype.sum_equiv E.toEquiv _ _ (fun x=>by simp)

theorem binary_match_zero (u : H → ℤ) (E : H ≃+ H) (j a b : ℕ) (bp : 0<b)
    (act : ∀x:H,2^a • x=E x) (identity : ∀x:H,2^b • x=x)
    (all : ∀x:H,(2:ℤ)^j∣corr u x) (t : H) :
    (2:ℤ)^j∣matched (fun x=>u (E.symm x)) u t := by
  classical
  let A := AddMonoidAlgebra ℤ H
  let B := AddMonoidAlgebra (ZMod 2) H
  let red : A →+* B := AddMonoidAlgebra.mapRingHom H (Int.castRingHom _)
  let sigma : A →+* A := AddMonoidAlgebra.mapDomainRingHom ℤ E.toAddMonoidHom
  have coeff (X:A) (i:H) : (red X).coeff i=(X.coeff i:ZMod 2) := by
    exact AddMonoidAlgebra.coeff_mapRingHom (R:=ℤ) (S:=ZMod 2) (M:=H) (Int.castRingHom (ZMod 2)) X i
  have kernel (X:A) : red X=0 ↔ (2:A)∣X := by
    rw [←show ((2:ℤ):A)=2 by norm_num,scalar_dvd]
    constructor
    · intro h i
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
      rw [←coeff,h]; rfl
    · intro h
      apply AddMonoidAlgebra.ext; ext i
      exact (coeff X i).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (h i))
  have cancel (X Y:A) (eq : 2*X=2*Y) : X=Y := by
    apply AddMonoidAlgebra.ext; ext i
    have hc := congrArg (fun Z:A=>Z.coeff i) eq
    change (((2:ℤ):A)*X).coeff i=(((2:ℤ):A)*Y).coeff i at hc
    have h' := (scalar_coeff 2 X i).symm.trans (hc.trans (scalar_coeff 2 Y i))
    omega
  have rep (X:A) : red X=forward (fun i:H=>(X.coeff i:ZMod 2)) := by
    apply AddMonoidAlgebra.ext; ext i; rw [coeff,forward_coeff]
  have base : 2≤2^b := Nat.le_pow bp
  have stable (X:A) : (red X)^(2^b-2+2)=red X := by
    rw [Nat.sub_add_cancel base,rep,frobenius_forward]
    simp only [identity,forward]
  have frob (X:A) : red (sigma X)=(red X)^(2^a) := by
    have inp : forward (fun i:H=>X.coeff i)=X := by apply AddMonoidAlgebra.ext; ext i; simp
    have out : sigma X=forward (fun i:H=>X.coeff (E.symm i)) := by
      conv_lhs => rw [←inp]
      exact binary_action E _
    calc
      red (sigma X)=forward (fun i:H=>((sigma X).coeff i:ZMod 2)) := rep _
      _=forward (fun i:H=>(X.coeff (E.symm i):ZMod 2)) := by
        rw [out]; apply congrArg forward; funext i; rw [forward_coeff]
      _=(red X)^(2^a) := by
        rw [rep,frobenius_forward]
        simp only [act,forward]
        exact Fintype.sum_equiv E.symm.toEquiv _ _ (fun x=>by simp)
  have init : (2:A)^j∣forward u*backward u := by
    have h₀ := (scalar_dvd ((2:ℤ)^j) (forward u*backward u)).mpr (fun i=>by
      rw [cross_coeff]; simpa [corr,add_comm,mul_comm] using all i)
    simpa only [Int.cast_pow,Int.cast_ofNat] using h₀
  have h:=binary_frobenius_lift red sigma (2^b-2) (2^a) (pow_pos (by decide) a)
              kernel cancel stable frob j (forward u) (backward u) init
  change (2:A)^j∣(AddMonoidAlgebra.mapDomainRingHom ℤ E.toAddMonoidHom (forward u))*backward u at h
  rw [binary_action] at h
  have hc := (scalar_dvd ((2:ℤ)^j) (forward (fun x=>u (E.symm x))*backward u)).mp (by
    simpa only [Int.cast_pow,Int.cast_ofNat] using h)
  simpa only [matched_shift,cross_coeff] using hc t

theorem binary_multiplier_dvd (u : H → ℤ) (n l : ℤ) (flat : ∀t,corr u t=(if t=0 then n else 0)+l)
    (j a b : ℕ) (bp : 0<b) (dn : (2:ℤ)^j∣n) (cop : IsCoprime ((2:ℤ)^j) (Fintype.card H:ℤ))
    (E : H ≃+ H) (act : ∀x:H,2^a • x=E x) (identity : ∀x:H,2^b • x=x) (t : H) :
    (2:ℤ)^j∣matched (fun x=>u (E.symm x)) u t-l := by
  let m:ℤ:=Fintype.card H
  let z:=fun x=>m*u x-mass u
  let d:=fun x=>u (E.symm x)
  have sq:=mass_from_flat u n l flat
  change (mass u)^2=n+m*l at sq
  have ca (f:H→ℤ) (t:H) : corr f t=matched f f (-t) := by simp [matched,corr]
  obtain ⟨w,hw⟩:=dn
  have divis (t:H) : (2:ℤ)^j∣corr z t := by
    rw [ca]; dsimp only [z,m]; rw [centered_match,←ca,flat]
    by_cases tz:t=0
    · simp only [tz,ite_true]
      refine ⟨(m^2-m)*w,?_⟩
      change m^2*(n+l)-m*mass u*mass u=_
      linear_combination -m*sq+(m^2-m)*hw
    · simp only [ite_eq_right tz,zero_add]
      refine ⟨-m*w,?_⟩
      change m^2*l-m*mass u*mass u=_
      linear_combination -m*sq-m*hw
  have lifted:=binary_match_zero z E j a b bp act identity divis t
  have md : mass d=mass u := equiv_mass E.symm.toEquiv u
  have eq : (fun x=>z (E.symm x))=fun x=>m*d x-mass d := by simp [d,z,md]
  rw [eq] at lifted
  change (2:ℤ)^j∣matched (fun x=>m*d x-mass d) (fun x=>m*u x-mass u) t at lifted
  rw [centered_match,md] at lifted
  obtain ⟨w',hw'⟩:=lifted
  have dv : (2:ℤ)^j∣m^2*(matched d u t-l) := by
    refine ⟨w'+m*w,?_⟩
    change m^2*matched d u t-m*mass u*mass u=(2:ℤ)^j*w' at hw'
    linear_combination hw'+m*sq+m*hw
  have cop₂ : IsCoprime ((2:ℤ)^j) (m^2) := cop.pow_right
  exact cop₂.dvd_of_dvd_mul_left dv

#print axioms binary_multiplier_dvd

end Signed39.Contraction
