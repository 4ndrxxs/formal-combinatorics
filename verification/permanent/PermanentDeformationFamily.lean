import PermanentDirectionalJet
import PermanentWeightedArrow

/-! Differential identities along the linear family of weighted arrow zeros. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder PermanentJets
namespace PermanentDeformation
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

def parameter {R : Type*} [CommRing R] (s : I→R) : Bigger I → R
  | (some i,some j) => if i=j then s i else 0
  | (some i,none) => s i
  | (none,some j) => s j
  | (none,none) => -(∑ i,s i)

def wt {R : Type*} [CommRing R] (s : I→R) : Option I→R := Option.elim' 0 s

theorem weighted_parameter {R : Type*} [CommRing R] (s : I→R) :
    PermanentArrow.Weighted.board (none:Option I) (wt s)=parameter s := by
  funext ⟨i,j⟩
  cases i <;> cases j <;>
    simp [PermanentArrow.Weighted.board,PermanentArrow.Weighted.total,parameter,wt,Fintype.sum_option]

theorem parameter_one :
    parameter (fun _ : I ↦ (1:K))=PermanentArrow.point K (none:Option I) := by
  funext ⟨i,j⟩
  cases i <;> cases j <;> simp [parameter,PermanentArrow.point]

def rect (K : Type*) [Field K] (i j : I) : Bigger I→K :=
  Pi.single (old (i,j)) 1-Pi.single (left i) 1-Pi.single (right j) 1+Pi.single corner 1

theorem dir_rect (i j : I) (p : MvPolynomial (Bigger I) K) :
    dir (rect K i j) p=pderiv (old (i,j)) p-pderiv (left i) p-pderiv (right j) p+pderiv corner p := by
  simp [rect,dir_addv,dir_subv,dir_single]

def lift (p : MvPolynomial (Bigger I) K) : MvPolynomial I K := eval₂Hom C (parameter (R:=MvPolynomial I K) X) p

theorem lift_dir (d : I→K) (p : MvPolynomial (Bigger I) K) :
    dir d (lift p)=lift (dir (parameter d) p) := by
  apply affine_chain
  rintro ⟨i,j⟩
  cases i with
  | none => cases j <;> simp [parameter]
  | some i =>
    cases j with
    | none => simp [parameter]
    | some j => by_cases eq : i=j <;> simp [parameter,eq]

theorem eval_lift (s : I→K) (p : MvPolynomial (Bigger I) K) : eval s (lift p)=eval (parameter s) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [lift]
  | add p q hp hq => change eval s (bind₁ _ (p+q))=_;change eval s (bind₁ _ p)=_ at hp;change eval s (bind₁ _ q)=_ at hq;simp [hp,hq]
  | mul_X p i =>
    rename_i hp
    change eval s (bind₁ _ (p*X i))=_
    change eval s (bind₁ _ p)=_ at hp
    obtain ⟨a,b⟩ := i
    cases a with
    | none => cases b <;> simp [parameter,hp]
    | some a => cases b with
      | none => simp [parameter,hp]
      | some b => by_cases h : a=b <;> simp [parameter,hp,h]

private theorem map_per {R S T : Type*} [CommRing R] [CommRing S] [Fintype T] [DecidableEq T] (h : R→+*S) :
    MvPolynomial.map h (per R T)=per S T := by
  simp [per,Matrix.permanent,PermanentCuts.generic]

private theorem lift_grad (e : Bigger I) :
    lift (pderiv e (per K (Option I)))=gradAt (parameter (R:=MvPolynomial I K) X) e := by
  change eval₂ C _ _=_
  rw [eval₂_eq_eval_map,←pderiv_map,map_per,grad_formula]

private theorem lift_hess (a b : Bigger I) :
    lift (pderiv a (pderiv b (per K (Option I))))=
      hessian (per (MvPolynomial I K) (Option I)) (parameter (R:=MvPolynomial I K) X) a b := by
  change eval₂ C _ _=_
  rw [eval₂_eq_eval_map,←pderiv_map,←pderiv_map,map_per]
  rfl

def monomialOn (K : Type*) [Field K] (s : Finset I) : MvPolynomial I K := ∏ i ∈ s,X i
def full (K : Type*) [Field K] (I : Type*) [Fintype I] : MvPolynomial I K := ∏ i,X i
def missing (K : Type*) [Field K] (i : I) : MvPolynomial I K := monomialOn K (univ.erase i)

theorem universal_laws (i j : I) (ij : i≠j) (v : Bigger I) :
    lift (pderiv corner (per K (Option I)))=full K I ∧
    lift (dir (rect K i j) (per K (Option I)))=0 ∧
    lift (dir (rect K i j) (pderiv v (per K (Option I))))=
      (if v=old (j,i) then -2*(missing K i+missing K j) else 0) := by
  let s : I→MvPolynomial I K := X
  obtain ⟨hc,hf,hr⟩ := PermanentArrow.Weighted.all_weighted none (some i) (some j) (wt s) v
    (by simp) (by simp) (by simpa using ij)
  have pro (a : I) : PermanentArrow.Weighted.skip (none:Option I) (some a) (wt s)=missing K a := by
    unfold PermanentArrow.Weighted.skip
    rw [Fintype.prod_option]
    simp [wt,missing,monomialOn,s,Finset.prod_ite,Finset.filter_ne']
  constructor
  · rw [lift_grad,←weighted_parameter]
    simpa [corner,PermanentArrow.Weighted.prodAll,Fintype.prod_option,wt,s,full] using hc
  constructor
  · rw [dir_rect]
    change (eval₂Hom C _) _=_
    simp only [map_add,map_sub]
    change lift _-lift _-lift _+lift _=_
    rw [lift_grad,lift_grad,lift_grad,lift_grad,←weighted_parameter]
    exact hf
  · rw [dir_rect]
    change (eval₂Hom C _) _=_
    simp only [map_add,map_sub]
    change lift _-lift _-lift _+lift _=_
    rw [lift_hess,lift_hess,lift_hess,lift_hess,←weighted_parameter]
    rw [pro,pro] at hr
    simpa [PermanentArrow.Weighted.rowJet,old,left,right,corner,s] using hr

end PermanentDeformation
