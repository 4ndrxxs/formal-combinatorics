import PermanentPolynomialCurveJets
import PermanentRankSpecialization

/-! Polynomial Hessian columns and their first surviving coefficients. -/
noncomputable section
open Matrix Finset MvPolynomial PermanentFive PermanentBorder PermanentJets PermanentCurve QuinticPencil
namespace PermanentDeformation
variable {K J : Type*} [Field K] [Fintype J] [DecidableEq J]

def imagePoly (d : Option J→K) (v : Cells J) : Polynomial K :=
  subst (curve K J) (dir (parameter d) (pderiv v (permP K J)))+
    Polynomial.X*subst (curve K J) (dir (correction d) (pderiv v (permP K J)))

def imageDiv (d : Option J→K) (v : Cells J) := (imagePoly d v).divX.divX

theorem image_low (two : (2:K)≠0) (d : Option J→K) (zd : ∑ i,d i=0) (v : Cells J) :
    (imagePoly d v).coeff 0=0 ∧ (imagePoly d v).coeff 1=0 := by
  have c := curve_taylor two (dir (parameter d) (pderiv v (permP K J)))
  have g := curve_taylor two (dir (correction d) (pderiv v (permP K J)))
  simp [imagePoly,Polynomial.coeff_X_mul,c.1,c.2.1,g.1,parameter_kernel d zd v,cancel_first two d zd v]

theorem image_factor (two : (2:K)≠0) (d : Option J→K) (zd : ∑ i,d i=0) (v : Cells J) :
    imageDiv d v*Polynomial.X^2=imagePoly d v := by
  let f := imagePoly d v
  obtain ⟨h0,h1⟩ := image_low two d zd v
  have f0 : f.coeff 0=0 := h0
  have f1 : f.divX.coeff 0=0 := by simpa only [Polynomial.coeff_divX] using h1
  have a := Polynomial.divX_mul_X_add f
  have b := Polynomial.divX_mul_X_add f.divX
  simp only [f0,f1,map_zero,add_zero] at a b
  change f.divX.divX*Polynomial.X^2=f
  rw [pow_two,←mul_assoc,b,a]

theorem subst_eval {I : Type*} (x : I→Polynomial K) (t : K) (p : MvPolynomial I K) :
    Polynomial.eval t (subst x p)=eval (Polynomial.eval t ∘ x) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [subst]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [subst] at hp ⊢;exact Or.inl hp

theorem image_eval (t : K) (d : Option J→K) (v : Cells J) :
    Polynomial.eval t (imagePoly d v)=
      (hessian (permP K J) (Polynomial.eval t ∘ curve K J) *ᵥ (parameter d+t • correction d)) v := by
  simp only [imagePoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,subst_eval,dir_hessian,
    Matrix.mulVec_add,Matrix.mulVec_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]

omit [DecidableEq J] in
private theorem sum_pair (x : Cells J→Polynomial K) (u y : Cells J→K) (p : MvPolynomial (Cells J) K) :
    (∑ v,Polynomial.C (u v)*subst x (dir y (pderiv v p)))=subst x (dir y (dir u p)) := by
  rw [dir_apply u]
  simp [subst]

theorem image_pair (d e : Option J→K) :
    (∑ v,Polynomial.C (parameter e v)*imagePoly d v)=
      subst (curve K J) (dir (parameter d) (dir (parameter e) (permP K J)))+
      Polynomial.X * subst (curve K J) (dir (correction d) (dir (parameter e) (permP K J))) := by
  simp only [imagePoly,mul_add,Finset.sum_add_distrib]
  rw [sum_pair,←sum_pair (curve K J) (parameter e) (correction d),Finset.mul_sum]
  congr 1
  apply sum_congr rfl
  intro v _
  ring

theorem image_reduced [Nonempty J] (two : (2:K)≠0) (d e : Option J→K)
    (zd : ∑ i,d i=0) (ze : ∑ i,e i=0) :
    (∑ v,parameter e v*(imageDiv d v).coeff 0)= -2*(∑ j,(d none-d (some j))*(e none-e (some j))) := by
  have h := congrArg (fun f : Polynomial K ↦ f.coeff 2) (image_pair d e)
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,Polynomial.coeff_add,Polynomial.coeff_X_mul] at h
  have first := (curve_taylor two (dir (parameter d) (dir (parameter e) (permP K J)))).2.2
  have second := (curve_taylor two (dir (correction d) (dir (parameter e) (permP K J)))).2.1
  have form := corrected_second two d e zd ze
  have hh : atOne (dir (direction K J) (dir (direction K J)
      (dir (parameter d) (dir (parameter e) (permP K J)))))+
      2*atOne (dir (bend K J) (dir (parameter d) (dir (parameter e) (permP K J))))+
      2*atOne (dir (direction K J) (dir (correction d) (dir (parameter e) (permP K J))))= -4*(∑ j,(d none-d (some j))*(e none-e (some j)))
      := by simpa only [dir_comm] using form
  simp only [imageDiv,Polynomial.coeff_divX]
  apply mul_left_cancel₀ two
  linear_combination 2*h + first + 2*second + hh

end PermanentDeformation
