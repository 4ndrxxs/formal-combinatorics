import PermanentBorderExpansion

/-! Differential identities at an identity-bordered matrix. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial PermanentFive QuinticPencil
namespace PermanentBorder
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
abbrev CellOf (I : Type*) := I × I
abbrev Bigger (I : Type*) := Option I × Option I
def old (u : CellOf I) : Bigger I := (some u.1,some u.2)
def corner : Bigger I := (none,none)
def left (r : I) : Bigger I := (some r,none)
def right (j : I) : Bigger I := (none,some j)

def extend (z : CellOf I → R) : Bigger I → R
  | (some r,some i) => z (r,i)
  | (none,none) => 1
  | _ => 0

def borderCoef (R : Type*) [CommRing R] {I : Type*} [Fintype I] [DecidableEq I] (r j : I) :
    MvPolynomial (Bigger I) R :=
  gradAt (inside (PermanentCuts.generic R (Option I))) (r,j)

theorem polynomial_border :
    per R (Option I)=X corner*rename old (per R I)+
      ∑ r : I, ∑ j : I, X (left r)*X (right j)*borderCoef R r j := by
  have h := permanent_border (PermanentCuts.generic R (Option I))
  have e : (core (PermanentCuts.generic R (Option I))).permanent=rename old (per R I) := by
    simp [per,core,Matrix.permanent,PermanentCuts.generic,old]
  rw [e] at h
  exact h

@[simp] theorem eval_borderCoef (z : CellOf I → R) (r j : I) :
    eval (extend z) (borderCoef R r j)=gradAt z (r,j) := by
  simp [borderCoef,gradAt,inside,PermanentCuts.generic,extend,apply_ite]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem eval_lift (z : CellOf I → R) (p : MvPolynomial (CellOf I) R) :
    eval (extend z) (rename old p)=eval z p := by rw [eval_rename];rfl

omit [Fintype I] [DecidableEq I] in
theorem old_inj : Function.Injective (old : CellOf I → Bigger I) := by
  rintro ⟨r,i⟩ ⟨s,j⟩ h
  simpa [old] using h

omit [Fintype I] [DecidableEq I] in
theorem outside_deriv (p : MvPolynomial (CellOf I) R) (v : Bigger I)
    (out : ∀ u : CellOf I, old u≠v) : pderiv v (rename old p)=0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨u,_,hu⟩ := mem_vars_rename old p h
  exact out u hu

section Leibniz
variable {A : Type*} [DecidableEq A]
def delta (R : Type*) [CommRing R] (a b : A) : R := if a=b then 1 else 0

@[simp] theorem eval_dX (w : A → R) (a b : A) : eval w (pderiv a (X b))=delta R a b := by
  by_cases h : a=b
  · subst b
    simp [delta]
  · simp [delta,h,pderiv_X_of_ne (Ne.symm h)]

@[simp] theorem ddX (a b c : A) : pderiv a (pderiv b (X (R:=R) c))=0 := by
  by_cases h : c=b
  · subst c
    simp
  · simp [pderiv_X_of_ne h]

theorem d_pair (w : A → R) (a u v : A) (p : MvPolynomial A R) (wu : w u=0) (wv : w v=0) :
    eval w (pderiv a (X u*X v*p))=0 := by
  simp [wu,wv]

theorem dd_pair (w : A → R) (a b u v : A) (p : MvPolynomial A R) (wu : w u=0) (wv : w v=0) :
    eval w (pderiv a (pderiv b (X u*X v*p)))=
      (delta R b u*delta R a v+delta R a u*delta R b v)*eval w p := by
  simp only [pderiv_mul,map_add,map_mul,eval_dX,eval_X,ddX,map_zero,wu,wv]
  ring

theorem d_unit (w : A → R) (a v : A) (p : MvPolynomial A R) (wv : w v=1) :
    eval w (pderiv a (X v*p))=delta R a v*eval w p+eval w (pderiv a p) := by
  simp only [pderiv_mul,map_add,map_mul,eval_dX,eval_X,wv]
  ring

theorem dd_unit (w : A → R) (a b v : A) (p : MvPolynomial A R) (wv : w v=1) :
    eval w (pderiv a (pderiv b (X v*p)))=
      delta R b v*eval w (pderiv a p)+delta R a v*eval w (pderiv b p)+eval w (pderiv a (pderiv b p)) := by
  simp only [pderiv_mul,map_add,map_mul,eval_dX,eval_X,ddX,map_zero,wv]
  ring
end Leibniz

#print axioms polynomial_border
end PermanentBorder
