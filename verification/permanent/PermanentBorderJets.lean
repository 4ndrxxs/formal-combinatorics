import PermanentBorderPolynomial

/-! Explicit gradient and Hessian blocks after adjoining a diagonal one. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial PermanentFive QuinticPencil
namespace PermanentBorder
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

def pad (f : CellOf I → R) : Bigger I → R
  | (some r,some j) => f (r,j)
  | _ => 0

def value (z : CellOf I → R) : R := eval z (per R I)
def cofactor (z : CellOf I → R) : Matrix I I R := Matrix.of fun r j ↦ gradAt z (r,j)

omit [Fintype I] [DecidableEq I] in
private theorem lift_first (z : CellOf I → R) (p : MvPolynomial (CellOf I) R) (u : Bigger I) :
    eval (extend z) (pderiv u (rename old p))=pad (fun i ↦ eval z (pderiv i p)) u := by
  rcases u with ⟨_|r,_|j⟩
  all_goals first
    | rw [outside_deriv p _ (by rintro ⟨s,i⟩; simp [old]),map_zero]; rfl
    | exact (congrArg (eval (extend z)) (pderiv_rename old_inj (r,j) p)).trans (eval_lift _ _)

omit [Fintype I] [DecidableEq I] in
private theorem lift_second (z : CellOf I → R) (p : MvPolynomial (CellOf I) R) (u v : Bigger I) :
    eval (extend z) (pderiv u (pderiv v (rename old p)))=
      pad (fun f ↦ pad (fun e ↦ eval z (pderiv e (pderiv f p))) u) v := by
  rcases v with ⟨_|r,_|j⟩
  all_goals first
    | rw [outside_deriv p _ (by rintro ⟨s,i⟩; simp [old]),map_zero,map_zero]; rfl
    | exact (congrArg (fun q ↦ eval (extend z) (pderiv u q)) (pderiv_rename old_inj (r,j) p)).trans
        (lift_first z (pderiv (r,j) p) u)

theorem value_extend (z : CellOf I → R) : value (extend z)=value z := by
  rw [value,polynomial_border]
  simp [corner,left,right,extend,value]

theorem grad_extend (z : CellOf I → R) (u : Bigger I) :
    gradAt (extend z) u = delta R u corner*value z+pad (gradAt z) u := by
  rw [←grad_formula,polynomial_border]
  have cu : extend z corner=1 := rfl
  have zu (r : I) : extend z (left r)=0 := rfl
  have zv (j : I) : extend z (right j)=0 := rfl
  simp only [map_add,map_sum,d_unit (extend z) u corner _ cu,d_pair (extend z) u _ _ _ (zu _) (zv _),
    eval_lift,lift_first,grad_formula,Finset.sum_const_zero,add_zero,value]

def hessBlock (z : CellOf I → R) : Matrix (Bigger I) (Bigger I) R := Matrix.of fun u v ↦
  match u,v with
  | (some r,some i),(some s,some j) => hessian (per R I) z (r,i) (s,j)
  | (none,none),(some r,some j) | (some r,some j),(none,none) => gradAt z (r,j)
  | (some r,none),(none,some j) | (none,some j),(some r,none) => gradAt z (r,j)
  | _,_ => 0

theorem hessian_extend (z : CellOf I → R) :
    hessian (per R (Option I)) (extend z)=hessBlock z := by
  ext u v
  change eval (extend z) (pderiv u (pderiv v (per R (Option I))))=_
  rw [polynomial_border]
  have cu : extend z corner=1 := rfl
  have zu (r : I) : extend z (left r)=0 := rfl
  have zv (j : I) : extend z (right j)=0 := rfl
  simp only [map_add,map_sum,dd_unit (extend z) u v corner _ cu,dd_pair (extend z) u v _ _ _
    (zu _) (zv _),lift_first,lift_second,eval_borderCoef,grad_formula]
  rcases u with ⟨_|r,_|i⟩ <;> rcases v with ⟨_|s,_|j⟩ <;>
    simp [hessBlock,delta,corner,left,right,pad,ite_mul,mul_ite,hessian]

#print axioms grad_extend
#print axioms hessian_extend
end PermanentBorder
