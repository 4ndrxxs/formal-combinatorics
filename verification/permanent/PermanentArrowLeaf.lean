import PermanentOrderTransport

/-! Adding a leaf attached to one designated index preserves the restricted
permanent polynomial, hence every Hessian entry in the old coordinates. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

def lower (c : I) (z : CellOf I → R) (e : CellOf I) : R :=
  z e - (if e=(c,c) then 1 else 0)

def leaf (c : I) (z : CellOf I → R) : Bigger I → R
  | (some i,some j) => lower c z (i,j)
  | (some i,none) => if i=c then 1 else 0
  | (none,some j) => if j=c then 1 else 0
  | (none,none) => 1

def matrixOf (z : CellOf I → R) : Matrix I I R := Matrix.of fun i j ↦ z (i,j)

theorem lower_grad (c : I) (z : CellOf I → R) :
    gradAt (lower c z) (c,c)=gradAt z (c,c) := by
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

theorem lower_permanent (c : I) (z : CellOf I → R) :
    (matrixOf (lower c z)).permanent=(matrixOf z).permanent-gradAt z (c,c) := by
  unfold Matrix.permanent gradAt
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp only [matrixOf,Matrix.of_apply]
  rw [←Finset.mul_prod_erase univ (fun j : I ↦ lower c z (p j,j)) (mem_univ c),
    ←Finset.mul_prod_erase univ (fun j : I ↦ z (p j,j)) (mem_univ c)]
  have rest : (∏ j ∈ univ.erase c, lower c z (p j,j))=∏ j ∈ univ.erase c, z (p j,j) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [lower,(Finset.mem_erase.mp hj).1]
  rw [rest]
  by_cases hp : p c=c <;> simp [lower,hp,sub_mul]

theorem leaf_permanent (c : I) (z : CellOf I → R) :
    (matrixOf (leaf c z)).permanent=(matrixOf z).permanent := by
  rw [permanent_border]
  have a : core (matrixOf (leaf c z))=matrixOf (lower c z) := rfl
  have b : inside (matrixOf (leaf c z))=lower c z := rfl
  rw [a,b,lower_permanent]
  simp [matrixOf,leaf,ite_mul,mul_ite,lower_grad]

def spec (c : I) : MvPolynomial (Bigger I) R →+* MvPolynomial (CellOf I) R :=
  eval₂Hom C (leaf c (fun e ↦ X e))

omit [Fintype I] in
@[simp] theorem spec_X (c : I) (v : Bigger I) : spec (R:=R) c (X v)=leaf c (fun e ↦ X e) v := by
  simp [spec]
omit [Fintype I] in
@[simp] theorem spec_C (c : I) (a : R) : spec c (C a)=C a := by simp [spec]

theorem spec_per (c : I) : spec c (per R (Option I))=per R I := by
  simpa [per,Matrix.permanent,PermanentCuts.generic,matrixOf] using
    (leaf_permanent c (fun e : CellOf I ↦ X (R:=R) e))

omit [Fintype I] in
theorem deriv_spec (c : I) (p : MvPolynomial (Bigger I) R) (e : CellOf I) :
    pderiv e (spec c p)=spec c (pderiv (old e) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p v hp =>
    simp only [map_mul,pderiv_mul,map_add,hp,spec_X]
    apply congrArg₂ (·+·) rfl
    apply congrArg (spec c p * ·)
    rcases e with ⟨a,b⟩
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
        change pderiv (a,b) (X (i,j)-(if (i,j)=(c,c) then 1 else 0))=
          spec c (pderiv (old (a,b)) (X (old (i,j))))
        have constant : pderiv (a,b) (if (i,j)=(c,c) then (1:MvPolynomial (CellOf I) R) else 0)=0 := by
          split <;> simp
        rw [map_sub,constant,sub_zero]
        by_cases h : (i,j)=(a,b)
        · rw [h]
          simp
        · rw [pderiv_X_of_ne h,pderiv_X_of_ne (old_inj.ne h),map_zero]

omit [Fintype I] in
theorem eval_spec (c : I) (p : MvPolynomial (Bigger I) R) (z : CellOf I → R) :
    eval z (spec c p)=eval (leaf c z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p v hp =>
    simp only [map_mul,hp,spec_X,eval_X]
    apply congrArg ((eval (leaf c z)) p * ·)
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

theorem leaf_hessian (c : I) (z : CellOf I → R) (e f : CellOf I) :
    hessian (per R (Option I)) (leaf c z) (old e) (old f)=hessian (per R I) z e f := by
  change eval _ (pderiv _ (pderiv _ _))=eval _ (pderiv _ (pderiv _ _))
  rw [←eval_spec,←deriv_spec,←deriv_spec,spec_per]

theorem leaf_gradient (c : I) (z : CellOf I → R) (e : CellOf I) :
    gradAt (leaf c z) (old e)=gradAt z e := by
  rw [←grad_formula,←grad_formula,←eval_spec,←deriv_spec,spec_per]

#print axioms leaf_hessian
end PermanentArrow
