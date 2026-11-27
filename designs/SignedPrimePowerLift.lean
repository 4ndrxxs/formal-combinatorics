import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.GeomSum

/-! Lifting Frobenius-compatible automorphisms through arbitrary prime powers. -/

namespace Signed39.Contraction

section Lift

variable {R S : Type} [CommRing R] [CommRing S]

open Finset

private theorem power_lift (q : ℕ) (qp : 0<q) (red : R →+* S)
    (kernel : ∀x,red x=0 ↔ (q:R)∣x) {x y : R} (h : (q:R)∣x-y) (j : ℕ) :
    (q:R)^(j+1)∣x^(q^j)-y^(q^j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    let X:=x^(q^j)
    let Y:=y^(q^j)
    obtain ⟨a,ha⟩ : (q:R)^(j+1)∣X-Y := ih
    have eq : red X=red Y := by
      apply sub_eq_zero.mp
      rw [←map_sub]
      apply (kernel _).mpr
      refine ⟨(q:R)^j*a,?_⟩
      rw [ha,pow_succ]; ring
    let D:=∑i∈range q,X^i*Y^(q-1-i)
    have dz : red D=0 := by
      have zero : (q:S)=0 := by simpa using (kernel (q:R)).2 (dvd_refl _)
      change red (∑i∈range q,X^i*Y^(q-1-i))=0
      rw [map_sum]
      calc
        _=∑i∈range q,(red Y)^(q-1) := by
          apply sum_congr rfl; intro i hi
          rw [map_mul,map_pow red X i,map_pow red Y _,eq,←pow_add]
          have le : i≤q-1 := by have h:=mem_range.mp hi; omega
          rw [show i+(q-1-i)=q-1 by omega]
        _=0 := by simp [nsmul_eq_mul,zero]
    obtain ⟨b,hb⟩ : (q:R)∣D := (kernel _).mp dz
    refine ⟨a*b,?_⟩
    rw [pow_succ (q:ℕ) j,pow_mul,pow_mul]
    change X^q-Y^q=_
    change (∑i∈range q,X^i*Y^(q-1-i))=(q:R)*b at hb
    rw [←geom_sum₂_mul,hb,ha,pow_succ (q:R) (j+1)]
    ring

private theorem idempotent_positive_power {x : S} (h : x^2=x) (j : ℕ) (positive : 0<j) :
    x^j=x := by
  induction j with
  | zero => omega
  | succ j ih =>
    cases j with
    | zero => simp
    | succ j => rw [pow_succ,ih (by omega),←pow_two,h]

theorem prime_power_frobenius_lift (q : ℕ) (qp : 0<q) (red : R →+* S) (sigma : R →+* R) (h t : ℕ) (ht : 0<t)
    (kernel : ∀x, red x=0 ↔ (q:R)∣x)
    (cancel : ∀a b:R,(q:R)*a=q*b → a=b)
    (stable : ∀x:R,(red x)^(h+2)=red x)
    (frobenius : ∀x:R,red (sigma x)=(red x)^t)
    (j : ℕ) (x y : R) (div : (q:R)^j∣x*y) : (q:R)^j∣sigma x*y := by
  induction j generalizing x y with
  | zero => simp
  | succ j ih =>
    let z₀ := x^(h+1)
    let z := z₀^(q^j)
    have idem : (red z₀)^2=red z₀ := by
      dsimp only [z₀]
      rw [map_pow,←pow_mul,show (h+1)*2=h+(h+2) by omega,pow_add,stable,pow_succ]
    have hz : red z=red z₀ := by
      dsimp only [z]; rw [map_pow,idempotent_positive_power idem _ (pow_pos qp j)]
    have fixed : (q:R)∣sigma z₀-z₀ := (kernel _).mp (by
      rw [map_sub,frobenius,idempotent_positive_power idem t ht,sub_self])
    obtain ⟨a,ha⟩ : (q:R)^(j+1)∣sigma z-z := by
      simpa only [z,map_pow] using power_lift q qp red kernel fixed j
    have xz : red z₀*red x=red x := by
      rw [show red z₀=(red x)^(h+1) by simp [z₀],←pow_succ,stable]
    obtain ⟨u,hu⟩ : (q:R)∣(1-z)*x := (kernel _).mp (by
      rw [map_mul,map_sub,map_one,hz,sub_mul,one_mul,xz,sub_self])
    have dxz : x∣z := (dvd_pow_self x (by omega : h+1≠0)).trans
      (dvd_pow_self z₀ (pow_ne_zero j qp.ne'))
    obtain ⟨v,hv⟩ := dxz
    obtain ⟨w,hw⟩ := div
    have zy : z*y=(q:R)^(j+1)*(w*v) := by calc
      _=(x*y)*v := by rw [hv]; ring
      _=_ := by rw [hw]; ring
    have dy : (q:R)^j∣u*y := by
      refine ⟨(1-z)*w,cancel _ _ ?_⟩
      calc
        (q:R)*(u*y)=((1-z)*x)*y := by rw [hu]; ring
        _=(1-z)*(x*y) := by ring
        _=_ := by rw [hw,pow_succ]; ring
    obtain ⟨b,hb⟩ := ih u y dy
    have hu' := congrArg sigma hu
    simp only [map_mul,map_sub,map_one,map_natCast] at hu'
    have sx : sigma x=z*sigma x+(q:R)^(j+1)*a*sigma x+(q:R)*sigma u := by
      linear_combination hu'+sigma x*ha
    refine ⟨w*v*sigma x+a*sigma x*y+b,?_⟩
    calc
      sigma x*y=(z*y)*sigma x+(q:R)^(j+1)*(a*sigma x*y)+(q:R)*(sigma u*y) := by
        linear_combination y*sx
      _=_ := by rw [zy,hb,pow_succ]; ring

end Lift

end Signed39.Contraction
