import PermanentArrowLeaf

/-! Inserting a satellite of weight a multiplies the restricted permanent by a. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow.Weighted
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

def lower (a : R) (c : I) (z : CellOf I → R) (e : CellOf I) : R :=
  z e - (if e=(c,c) then a else 0)

def leaf (a : R) (c : I) (z : CellOf I → R) : Bigger I → R
  | (some i,some j) => lower a c z (i,j)
  | (some i,none) => if i=c then a else 0
  | (none,some j) => if j=c then a else 0
  | (none,none) => a

def matrixOf (z : CellOf I → R) : Matrix I I R := Matrix.of fun i j ↦ z (i,j)

theorem lower_grad (a : R) (c : I) (z : CellOf I → R) :
    gradAt (lower a c z) (c,c)=gradAt z (c,c) := by
  unfold gradAt
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p c=c
  · simp only [hp,ite_true]
    apply Finset.prod_congr rfl
    intro j hj
    have ne := (Finset.mem_erase.mp hj).1
    simp [lower,ne]
  · simp [hp]

theorem lower_permanent (a : R) (c : I) (z : CellOf I → R) :
    (matrixOf (lower a c z)).permanent=(matrixOf z).permanent-a*gradAt z (c,c) := by
  unfold Matrix.permanent gradAt
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [matrixOf,Matrix.of_apply]
  rw [←Finset.mul_prod_erase univ (fun j : I ↦ lower a c z (p j,j)) (mem_univ c),
    ←Finset.mul_prod_erase univ (fun j : I ↦ z (p j,j)) (mem_univ c)]
  have rest : (∏ j ∈ univ.erase c, lower a c z (p j,j))=∏ j ∈ univ.erase c, z (p j,j) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [lower,(Finset.mem_erase.mp hj).1]
  rw [rest]
  by_cases hp : p c=c <;> simp [lower,hp,sub_mul]

theorem leaf_permanent (a : R) (c : I) (z : CellOf I → R) :
    (matrixOf (leaf a c z)).permanent=a*(matrixOf z).permanent := by
  rw [permanent_border]
  have core_eq : core (matrixOf (leaf a c z))=matrixOf (lower a c z) := rfl
  have b : inside (matrixOf (leaf a c z))=lower a c z := rfl
  rw [core_eq,b,lower_permanent]
  simp [matrixOf,leaf,ite_mul,mul_ite,lower_grad]
  ring

def spec (a : R) (c : I) : MvPolynomial (Bigger I) R →+* MvPolynomial (CellOf I) R :=
  eval₂Hom C (leaf (C a) c (fun e ↦ X e))

omit [Fintype I] in
@[simp] theorem spec_X (a : R) (c : I) (v : Bigger I) : spec a c (X v)=leaf (C a) c (fun e ↦ X e) v := by
  simp [spec]
omit [Fintype I] in
@[simp] theorem spec_C (a : R) (c : I) (k : R) : spec a c (C k)=C k := by simp [spec]

theorem spec_per (a : R) (c : I) : spec a c (per R (Option I))=C a*per R I := by
  simpa [per,Matrix.permanent,PermanentCuts.generic,matrixOf] using
    (leaf_permanent (C a) c (fun e : CellOf I ↦ X (R:=R) e))

omit [Fintype I] in
theorem deriv_spec (a : R) (c : I) (p : MvPolynomial (Bigger I) R) (e : CellOf I) :
    pderiv e (spec a c p)=spec a c (pderiv (old e) p) := by
  induction p using MvPolynomial.induction_on with
  | C k => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p v hp =>
    simp only [map_mul,pderiv_mul,map_add,hp,spec_X]
    apply congrArg₂ (·+·) rfl
    apply congrArg (spec a c p * ·)
    rcases e with ⟨r,b⟩
    rcases v with ⟨i,j⟩
    cases i with
    | none =>
      cases j with
      | none => simp [leaf,old,pderiv_X]
      | some j => by_cases h : j=c <;> simp [leaf,old,h,pderiv_X]
    | some i =>
      cases j with
      | none => by_cases h : i=c <;> simp [leaf,old,h,pderiv_X]
      | some j =>
        change pderiv (r,b) (X (i,j)-(if (i,j)=(c,c) then C a else 0))=
          spec a c (pderiv (old (r,b)) (X (old (i,j))))
        have constant : pderiv (r,b) (if (i,j)=(c,c) then (C a:MvPolynomial (CellOf I) R) else 0)=0 := by
          split <;> simp
        rw [map_sub,constant,sub_zero]
        by_cases h : (i,j)=(r,b)
        · rw [h]
          simp
        · rw [pderiv_X_of_ne h,pderiv_X_of_ne (old_inj.ne h),map_zero]

omit [Fintype I] in
theorem eval_spec (a : R) (c : I) (p : MvPolynomial (Bigger I) R) (z : CellOf I → R) :
    eval z (spec a c p)=eval (leaf a c z) p := by
  induction p using MvPolynomial.induction_on with
  | C k => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p v hp =>
    simp only [map_mul,hp,spec_X,eval_X]
    apply congrArg ((eval (leaf a c z)) p * ·)
    rcases v with ⟨i,j⟩
    cases i with
    | none =>
      cases j with
      | none => simp [leaf]
      | some j => by_cases h : j=c <;> simp [leaf,h]
    | some i =>
      cases j with
      | none => by_cases h : i=c <;> simp [leaf,h]
      | some j => by_cases h : (i,j)=(c,c) <;> simp [leaf,lower,h]

theorem leaf_hessian (a : R) (c : I) (z : CellOf I → R) (e f : CellOf I) :
    hessian (per R (Option I)) (leaf a c z) (old e) (old f)=a*hessian (per R I) z e f := by
  change eval _ (pderiv _ (pderiv _ _))=a*eval _ (pderiv _ (pderiv _ _))
  rw [←eval_spec,←deriv_spec,←deriv_spec,spec_per]
  simp

theorem leaf_gradient (a : R) (c : I) (z : CellOf I → R) (e : CellOf I) :
    gradAt (leaf a c z) (old e)=a*gradAt z e := by
  rw [←grad_formula,←grad_formula,←eval_spec,←deriv_spec,spec_per]
  simp

#print axioms leaf_hessian
end PermanentArrow.Weighted
