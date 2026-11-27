import Quantum.Hadamard.PaleySign
import Quantum.Hadamard.PaleyCore

/-! The affine linear forms and projective quadratic-character weighing
matrix in Brouwer's symmetric design. All counting identities are integral. -/
noncomputable section
namespace Hadamard.Brouwer
open Finset Hadamard.PG

structure Geometry (q n : ℕ) [Fact q.Prime] (E P : Type) [Fintype E] [Fintype P] where
  value : P → E → ZMod q
  weight : P → P → ℤ
  zero : P → P → ℤ
  values : ∀ i j, (weight i j=0 ∧ zero i j=1) ∨
    ((weight i j=1 ∨ weight i j= -1) ∧ zero i j=0)
  cardE : Fintype.card E=q^(n+2)
  cardP : Fintype.card P=geom q (n+2)
  oneform : ∀ j (f : ZMod q → ℤ), (∑ x, f (value j x))=(q:ℤ)^(n+1)*∑ y,f y
  twoform : ∀ j k, j≠k → ∀ f g : ZMod q → ℤ,
    (∑ x,f (value j x)*g (value k x))=(q:ℤ)^n*(∑ y,f y)*(∑ y,g y)
  zerosum : ∀ j, (∑ i, zero i j)=(geom q (n+1):ℤ)
  zeropair : ∀ j k, j≠k → (∑ i,zero i j*zero i k)=(geom q n:ℤ)
  weightpair : ∀ j k, j≠k → (∑ i,weight i j*weight i k)=0

private theorem project_sum {F E : Type} [Field F] [Field E] [Algebra F E] [Fintype F]
    [DecidableEq F] [Fintype E] [DecidableEq E] (f : E → ℤ)
    (inv : ∀ c : F, c≠0 → ∀ x : E, f (algebraMap F E c*x)=f x) :
    ((Fintype.card F:ℤ)-1)*(∑ i : Projective F E, f (chooseRep F E i))+f 0 = ∑ x:E,f x := by
  have H := sum_project (fun i : Projective F E => f (chooseRep F E i))
  simp only [descend_project f inv] at H
  rw [←H]
  exact sum_units_with_zero f

theorem geometry {q n : ℕ} [Fact q.Prime] (q4 : q%4=3) {E : Type} [Field E]
    [Algebra (ZMod q) E] [Fintype E] [DecidableEq E] [FiniteDimensional (ZMod q) E]
    (L : E →ₗ[ZMod q] ZMod q) (nz : L≠0) (rank : Module.finrank (ZMod q) E=n+2) :
    Nonempty (Geometry q n E (Projective (ZMod q) E)) := by
  classical
  let F := ZMod q
  let P := Projective F E
  let rep := chooseRep F E
  let val (j:P) (x:E) := L ((rep j:E)*x)
  let ind (x:F) : ℤ := if x=0 then 1 else 0
  let chi := quadraticChar F
  have one (j:P) (f : F → ℤ) : (∑ x:E,f (val j x))=(q:ℤ)^(n+1)*∑ y,f y := by
    have e := Equiv.sum_comp (Equiv.mulLeft₀ (rep j:E) (rep j).ne_zero) (fun x:E => f (L x))
    have h := sum_linear L (form_surjective L nz) f
    rw [kernel_card L (form_surjective L nz),rank,Module.finrank_self,show n+2-1=n+1 by omega,
      ZMod.card,Nat.cast_pow] at h
    exact e.trans h
  have two (j k:P) (ne:j≠k) (f g : F → ℤ) :
      (∑ x:E,f (val j x)*g (val k x))=(q:ℤ)^n*(∑ y,f y)*(∑ y,g y) := by
    let b := rep k / rep j
    have pb : project F E b ≠ 1 := by
      change project F E (chooseRep F E k / chooseRep F E j) ≠ 1
      rw [map_div,project_chooseRep,project_chooseRep]
      exact div_ne_one.mpr ne.symm
    have hs := pair_surjective L nz (b:E) (nonscalar b pb)
    have h := sum_linear (pairForm L b) hs (fun y:F×F => f y.1*g y.2)
    rw [kernel_card _ hs,rank,Module.finrank_prod,Module.finrank_self,show n+2-(1+1)=n by omega,
      ZMod.card,Nat.cast_pow,Fintype.sum_prod_type] at h
    simp only [pair_apply,← mul_sum,← sum_mul] at h
    have e := Equiv.sum_comp (Equiv.mulLeft₀ (rep j:E) (rep j).ne_zero)
      (fun x:E => f (L x)*g (L ((b:E)*x)))
    have id (x:E) : (b:E)*((rep j:E)*x)=(rep k:E)*x := by
      dsimp [b]
      rw [←mul_assoc]
      simp
    simpa only [Equiv.mulLeft₀_apply,id,val,mul_assoc] using e.trans h
  have scal (j:P) (c:F) (x:E) : val j (algebraMap F E c*x)=c*val j x := by
    dsimp [val]
    rw [mul_left_comm,← Algebra.smul_def,L.map_smul,smul_eq_mul]
  have iz (j:P) : val j 0=0 := by simp [val]
  have indsum : ∑ x:F, ind x=1 := by simp [ind]
  have indzero : ind 0=1 := by simp [ind]
  have fieldcard : Fintype.card F=q := ZMod.card q
  have i0 (j:P) (c:F) (hc:c≠0) (x:E) :
      ind (val j (algebraMap F E c*x))=ind (val j x) := by simp [scal,ind,hc]
  have zsum (j:P) : (∑ i:P,ind (val j (rep i)))=(geom q (n+1):ℤ) := by
    have H := project_sum (fun x:E => ind (val j x)) (i0 j)
    change ((Fintype.card F:ℤ)-1)*(∑ i:P,ind (val j (rep i)))+ind (val j 0)=_ at H
    rw [one,iz] at H
    rw [fieldcard,indsum,indzero,mul_one] at H
    have hg := geom_int q (n+1)
    have hg0 : (q:ℤ)-1≠0 := by have := (Fact.out : q.Prime).two_le; omega
    apply mul_left_cancel₀ hg0
    linear_combination H-hg
  have zpair (j k:P) (ne:j≠k) : (∑ i:P,ind (val j (rep i))*ind (val k (rep i)))=
      (geom q n:ℤ) := by
    have H := project_sum (fun x:E => ind (val j x)*ind (val k x))
      (fun c hc x => by rw [i0 j c hc,i0 k c hc])
    change ((Fintype.card F:ℤ)-1)*(∑ i:P,ind (val j (rep i))*ind (val k (rep i)))+
      ind (val j 0)*ind (val k 0)=_ at H
    rw [two j k ne,iz,iz] at H
    rw [fieldcard,indsum,indzero,mul_one,mul_one,mul_one] at H
    have hg := geom_int q n
    have hg0 : (q:ℤ)-1≠0 := by have := (Fact.out : q.Prime).two_le; omega
    apply mul_left_cancel₀ hg0
    linear_combination H-hg
  have wpair (j k:P) (ne:j≠k) : (∑ i:P,chi (val j (rep i))*chi (val k (rep i)))=0 := by
    have H := project_sum (fun x:E => chi (val j x)*chi (val k x)) (fun c hc x => by
      rw [scal,scal,map_mul,map_mul]
      have cs : chi c*chi c=1 := by simpa [chi,pow_two] using quadraticChar_sq_one hc
      linear_combination chi (val j x)*chi (val k x)*cs)
    change ((Fintype.card F:ℤ)-1)*(∑ i:P,chi (val j (rep i))*chi (val k (rep i)))+
      chi (val j 0)*chi (val k 0)=_ at H
    rw [two j k ne,iz,iz] at H
    have sm : ∑ x:F,chi x=0 := quadraticChar_sum_zero
      (by rw [ZMod.ringChar_zmod_n]; omega : ringChar (ZMod q) ≠ 2)
    simp only [fieldcard,sm,show chi 0=0 by simp [chi],zero_mul,add_zero,mul_zero] at H
    have hg0 : (q:ℤ)-1≠0 := by have := (Fact.out : q.Prime).two_le; omega
    exact (mul_eq_zero.mp H).resolve_left hg0
  refine ⟨⟨val,fun i j => chi (val j (rep i)),fun i j => ind (val j (rep i)),?_,?_,?_,
    one,two,zsum,zpair,wpair⟩⟩
  · intro i j
    by_cases z : val j (rep i)=0
    · simp [chi,ind,z]
    · exact Or.inr ⟨quadraticChar_dichotomy z,by simp [ind,z]⟩
  · rw [Module.card_eq_pow_finrank (K := F),rank,ZMod.card]
  · rw [← Nat.card_eq_fintype_card,projective_card,rank,ZMod.card]

end Hadamard.Brouwer
