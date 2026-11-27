import PermanentStarCorrection

/-! A polynomial correction in a single column gives an exact zero of the
permanent. Its auxiliary scalar has constant term one and vanishing first
and second perturbations when the corner cofactor starts at one. -/
noncomputable section
open Finset MvPolynomial PermanentFive PermanentBorder PermanentJets PermanentCurve
namespace PermanentDeformation
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

theorem value_terms (x : I×I→R) : value x=∑ p : Equiv.Perm I,∏ j,x (p j,j) := by
  simp [value,per,Matrix.permanent,PermanentCuts.generic]

def editCol (x : I×I→R) (e : I×I) (h q : R) (v : I×I) : R :=
  if v.2=e.2 then h*x v+(if v.1=e.1 then q else 0) else x v

private theorem erased_col (x : I×I→R) (e : I×I) (h q : R) (p : Equiv.Perm I) :
    (∏ j ∈ univ.erase e.2,editCol x e h q (p j,j))=∏ j ∈ univ.erase e.2,x (p j,j) := by
  apply prod_congr rfl
  intro j hj
  simp [editCol,(mem_erase.mp hj).1]

theorem value_editCol (x : I×I→R) (e : I×I) (h q : R) :
    value (editCol x e h q)=h*value x+q*gradAt x e := by
  rw [value_terms,value_terms,gradAt,mul_sum,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [←mul_prod_erase univ (fun j ↦ editCol x e h q (p j,j)) (mem_univ e.2),erased_col,
    ←mul_prod_erase univ (fun j ↦ x (p j,j)) (mem_univ e.2)]
  by_cases g : p e.2=e.1 <;> simp [editCol,g] <;> ring

theorem grad_editCol (x : I×I→R) (e : I×I) (h q : R) : gradAt (editCol x e h q) e=gradAt x e := by
  simp only [gradAt,erased_col]

def multiplier (b : R) := 1-(b-1)+(b-1)^2

def zeroCorrection (x : I×I→R) (e : I×I) : I×I→R :=
  editCol x e (gradAt x e*multiplier (gradAt x e)) (-(multiplier (gradAt x e))*value x)

theorem correction_zero (x : I×I→R) (e : I×I) : value (zeroCorrection x e)=0 := by
  rw [zeroCorrection,value_editCol]
  ring

theorem correction_smooth (x : I×I→R) (e : I×I) : gradAt (zeroCorrection x e) e=gradAt x e :=
  grad_editCol _ _ _ _

variable {K J : Type*} [Field K] [Fintype J] [DecidableEq J]

def tangentLine (K J : Type*) [Field K] [Fintype J] [DecidableEq J] (v : Cells J) : Polynomial K :=
  Polynomial.C (base K J v)+Polynomial.X*Polynomial.C (direction K J v)

def curve (K J : Type*) [Field K] [Fintype J] [DecidableEq J] : Cells J→Polynomial K :=
  zeroCorrection (tangentLine K J) corner

theorem line_zero (v : Cells J) : (tangentLine K J v).coeff 0=base K J v := by
  simp [tangentLine]
theorem line_one (v : Cells J) : (tangentLine K J v).coeff 1=direction K J v := by
  simp [tangentLine]
theorem line_two (v : Cells J) : (tangentLine K J v).coeff 2=0 := by
  simp [tangentLine]

theorem subst_per (x : I×I→Polynomial K) : subst x (per K I)=value x := by
  simp [subst,value_terms,per,Matrix.permanent,PermanentCuts.generic]

theorem subst_grad (x : I×I→Polynomial K) (e : I×I) : subst x (pderiv e (per K I))=gradAt x e := by
  change eval₂ Polynomial.C x _=_
  rw [eval₂_eq_eval_map,←pderiv_map]
  have mv : MvPolynomial.map (Polynomial.C:K→+*Polynomial K) (per K I)=per (Polynomial K) I := by
    simp [per,Matrix.permanent,PermanentCuts.generic]
  rw [mv,grad_formula]

theorem line_per_jets (two : (2:K)≠0) :
    (value (tangentLine K J)).coeff 0=0 ∧ (value (tangentLine K J)).coeff 1=0 ∧
    (value (tangentLine K J)).coeff 2= -4*(Fintype.card J:K) := by
  have h := taylor (tangentLine K J) (base K J) (direction K J) 0 line_zero line_one line_two (permP K J)
  change _=_ ∧ _=_ ∧ _=atOne _+2*atOne _ at h
  rw [show subst (tangentLine K J) (permP K J)=_ from subst_per _,zero_direction] at h
  have val := (PermanentArrow.all_entries K (none:Option (Option J)) corner corner).1
  have one := normal_zero (fun _ : J ↦ (1:K))
  have dd := normal_pair (fun _ : J ↦ (1:K)) (fun _ : J ↦ (1:K))
  change atOne (dir (direction K J) (dir (direction K J) (permP K J)))=_ at dd
  simp only [_root_.mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at dd
  refine ⟨h.1.trans val,h.2.1.trans one,?_⟩
  have jet := h.2.2
  rw [dd] at jet
  simp [atOne] at jet
  apply (mul_left_cancel₀ two)
  linear_combination jet

theorem line_cofactor (K J : Type*) [Field K] [Fintype J] [DecidableEq J] :
    (gradAt (tangentLine K J) corner).coeff 0=1 := by
  rw [←subst_grad]
  have h := (taylor (tangentLine K J) (base K J) (direction K J) 0 line_zero line_one line_two
    (pderiv corner (permP K J))).1
  rw [grad_formula] at h
  exact h.trans (PermanentArrow.all_entries K (none:Option (Option J)) corner corner).2.1

end PermanentDeformation
