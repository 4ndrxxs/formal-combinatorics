import PermanentDirectionalJet

/-! The first three Taylor coefficients after polynomial substitution. The
second-order identity is integral and can be used in positive characteristic. -/
noncomputable section
open Finset MvPolynomial PermanentJets
namespace PermanentCurve
variable {K E : Type*} [Field K] [Fintype E]

def subst (x : E→Polynomial K) : MvPolynomial E K→+*Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C x

theorem mul_one (p q : Polynomial K) :
    (p*q).coeff 1=p.coeff 0*q.coeff 1+p.coeff 1*q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  simp [show Finset.antidiagonal (1:ℕ)={(0,1),(1,0)} from by decide]

theorem mul_two (p q : Polynomial K) :
    (p*q).coeff 2=p.coeff 0*q.coeff 2+p.coeff 1*q.coeff 1+p.coeff 2*q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  simp [show Finset.antidiagonal (2:ℕ)={(0,2),(1,1),(2,0)} from by decide,add_assoc]

theorem taylor (x : E→Polynomial K) (z u v : E→K)
    (h0 : ∀ i,(x i).coeff 0=z i) (h1 : ∀ i,(x i).coeff 1=u i) (h2 : ∀ i,(x i).coeff 2=v i)
    (p : MvPolynomial E K) :
    (subst x p).coeff 0=eval z p ∧
    (subst x p).coeff 1=eval z (dir u p) ∧
    2*(subst x p).coeff 2=eval z (dir u (dir u p))+2*eval z (dir v p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [subst,Polynomial.coeff_C]
  | add p q hp hq =>
    obtain ⟨a,b,c⟩ := hp
    obtain ⟨d,e,f⟩ := hq
    simp only [map_add,Polynomial.coeff_add]
    exact ⟨by rw [a,d],by rw [b,e],by linear_combination c+f⟩
  | mul_X p i hp =>
    obtain ⟨a,b,c⟩ := hp
    have xx : subst x (X i)=x i := by simp [subst]
    simp only [map_mul,xx,Polynomial.mul_coeff_zero,mul_one,mul_two,h0,h1,h2,
      Derivation.leibniz,smul_eq_mul,dir_X,dir_C,map_add,eval_X,eval_C,mul_zero,zero_add]
    exact ⟨by rw [a],by rw [a,b];ring,by rw [a,b];linear_combination z i*c⟩

theorem zero_direction (p : MvPolynomial E K) : dir (0:E→K) p=0 := by simp [dir_apply]

theorem dir_sumv {J : Type*} (s : Finset J) (u : J→E→K) :
    dir (∑ j ∈ s,u j)=∑ j ∈ s,dir (u j) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext1 p; simp
  | insert j s hj ih => simp [hj,dir_addv,ih]

theorem dir_pderiv [DecidableEq E] (u : E→K) (p : MvPolynomial E K) (v : E) :
    dir u (pderiv v p)=pderiv v (dir u p) := by
  rw [←dir_single (R:=K) v,dir_comm]

end PermanentCurve
