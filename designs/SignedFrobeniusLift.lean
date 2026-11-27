import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Lifting a binary Frobenius multiplier through powers of two on the odd group algebra. -/

namespace Signed39.Contraction

section Lift

variable {R S : Type} [CommRing R] [CommRing S]

private theorem square_lift {x y : R} (h : (2:R)∣x-y) (j : ℕ) :
    (2:R)^(j+1)∣x^(2^j)-y^(2^j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    obtain ⟨a,ha⟩ := ih
    have plus : x^(2^j)+y^(2^j)=2*((2:R)^j*a+y^(2^j)) := by
      rw [pow_succ (2:R) j] at ha
      linear_combination ha
    refine ⟨a*((2:R)^j*a+y^(2^j)),?_⟩
    rw [pow_succ (2:ℕ) j,pow_mul,pow_mul]
    calc
      _ = (x^(2^j)-y^(2^j))*(x^(2^j)+y^(2^j)) := by ring
      _ = _ := by rw [ha,plus,pow_succ (2:R) (j+1)]; ring

private theorem idempotent_positive_power {x : S} (h : x^2=x) (j : ℕ) (positive : 0<j) :
    x^j=x := by
  induction j with
  | zero => omega
  | succ j ih =>
    cases j with
    | zero => simp
    | succ j => rw [pow_succ,ih (by omega),←pow_two,h]

theorem binary_frobenius_lift (red : R →+* S) (sigma : R →+* R) (h t : ℕ) (ht : 0<t)
    (kernel : ∀x, red x=0 ↔ (2:R)∣x)
    (cancel : ∀a b:R,2*a=2*b → a=b)
    (stable : ∀x:R,(red x)^(h+2)=red x)
    (frobenius : ∀x:R,red (sigma x)=(red x)^t)
    (j : ℕ) (x y : R) (div : (2:R)^j∣x*y) : (2:R)^j∣sigma x*y := by
  induction j generalizing x y with
  | zero => simp
  | succ j ih =>
    let z₀ := x^(h+1)
    let z := z₀^(2^j)
    have idem : (red z₀)^2=red z₀ := by
      dsimp only [z₀]
      rw [map_pow,←pow_mul,show (h+1)*2=h+(h+2) by omega,pow_add,stable,pow_succ]
    have hz : red z=red z₀ := by
      dsimp only [z]; rw [map_pow,idempotent_positive_power idem _ (pow_pos (by decide) j)]
    have fixed : (2:R)∣sigma z₀-z₀ := (kernel _).mp (by
      rw [map_sub,frobenius,idempotent_positive_power idem t ht,sub_self])
    obtain ⟨a,ha⟩ : (2:R)^(j+1)∣sigma z-z := by
      simpa only [z,map_pow] using square_lift fixed j
    have xz : red z₀*red x=red x := by
      rw [show red z₀=(red x)^(h+1) by simp [z₀],←pow_succ,stable]
    obtain ⟨u,hu⟩ : (2:R)∣(1-z)*x := (kernel _).mp (by
      rw [map_mul,map_sub,map_one,hz,sub_mul,one_mul,xz,sub_self])
    have dxz : x∣z := (dvd_pow_self x (by omega : h+1≠0)).trans
      (dvd_pow_self z₀ (pow_ne_zero j (by decide : (2:ℕ)≠0)))
    obtain ⟨v,hv⟩ := dxz
    obtain ⟨w,hw⟩ := div
    have zy : z*y=(2:R)^(j+1)*(w*v) := by calc
      _=(x*y)*v := by rw [hv]; ring
      _=_ := by rw [hw]; ring
    have dy : (2:R)^j∣u*y := by
      refine ⟨(1-z)*w,cancel _ _ ?_⟩
      calc
        2*(u*y)=((1-z)*x)*y := by rw [hu]; ring
        _=(1-z)*(x*y) := by ring
        _=_ := by rw [hw,pow_succ]; ring
    obtain ⟨b,hb⟩ := ih u y dy
    have hu' := congrArg sigma hu
    simp only [map_mul,map_sub,map_one,map_ofNat] at hu'
    have sx : sigma x=z*sigma x+(2:R)^(j+1)*a*sigma x+2*sigma u := by
      linear_combination hu'+sigma x*ha
    refine ⟨w*v*sigma x+a*sigma x*y+b,?_⟩
    calc
      sigma x*y=(z*y)*sigma x+(2:R)^(j+1)*(a*sigma x*y)+2*(sigma u*y) := by
        linear_combination y*sx
      _=_ := by rw [zy,hb,pow_succ]; ring

end Lift

end Signed39.Contraction
