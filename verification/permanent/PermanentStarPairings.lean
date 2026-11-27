import PermanentDeformationProducts
import PermanentCurveJets

/-! Pairings of the rectangular normal directions at the arrow zero. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder PermanentJets PermanentCurve
namespace PermanentDeformation
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem atOne_add (p q : MvPolynomial (Bigger I) K) : atOne (p+q)=atOne p+atOne q := map_add _ _ _
theorem atOne_cmul (a : K) (p : MvPolynomial (Bigger I) K) : atOne (C a*p)=a*atOne p := by simp [atOne]
theorem atOne_sum {J : Type*} (s : Finset J) (p : J→MvPolynomial (Bigger I) K) :
    atOne (∑ j ∈ s,p j)=∑ j ∈ s,atOne (p j) := map_sum _ _ _

theorem rect_zero (i j : I) (ij : i≠j) :
    atOne (dir (rect K i j) (per K (Option I)))=0 := by
  rw [←atOne_lift,(universal_laws (K:=K) i j ij corner).2.1,map_zero]

theorem rect_row (i j : I) (ij : i≠j) (v : Bigger I) :
    atOne (dir (rect K i j) (pderiv v (per K (Option I))))=
      if v=old (j,i) then -4 else 0 := by
  rw [←atOne_lift,(universal_laws (K:=K) i j ij v).2.2]
  by_cases h : v=old (j,i)
  · simp [h,missing,monomialOn]
    ring
  · simp [h]

private theorem sum_pick {T : Type*} [Fintype T] [DecidableEq T] (y : T→K) (b : T) (a : K) :
    (∑ v,y v*(if v=b then a else 0))=a*y b := by simp [mul_ite,mul_comm]

theorem rect_pair (i j : I) (ij : i≠j) (y : Bigger I→K) :
    atOne (dir (rect K i j) (dir y (per K (Option I))))= -4*y (old (j,i)) := by
  rw [dir_apply y]
  simp only [map_sum,dir_const_mul,atOne_sum,atOne_cmul,rect_row i j ij]
  exact sum_pick y _ _

theorem rect_pair_third (i j : I) (ij : i≠j) (y : Bigger I→K) (d : I→K) (zd : ∑ i,d i=0) :
    atOne (dir (parameter d) (dir (rect K i j) (dir y (per K (Option I)))))=
      2*(d i+d j)*y (old (j,i)) := by
  rw [dir_apply y]
  simp only [map_sum,dir_const_mul,atOne_sum,atOne_cmul,rect_third i j ij _ d zd]
  exact sum_pick y _ _

theorem rect_pair_fourth (i j : I) (ij : i≠j) (y : Bigger I→K) (d e : I→K)
    (zd : ∑ i,d i=0) (ze : ∑ i,e i=0) :
    atOne (dir (parameter e) (dir (parameter d) (dir (rect K i j) (dir y (per K (Option I))))))=
      (-4*(d i*e i+d j*e j)+4*(∑ k,d k*e k))*y (old (j,i)) := by
  rw [dir_apply y]
  simp only [map_sum,dir_const_mul,atOne_sum,atOne_cmul,rect_fourth i j ij _ d e zd ze]
  exact sum_pick y _ _

variable {J : Type*} [Fintype J] [DecidableEq J]
abbrev Cells (J : Type*) := Bigger (Option J)
abbrev permP (K J : Type*) [Field K] [Fintype J] [DecidableEq J] := per K (Option (Option J))

def normal (a : J→K) : Cells J→K :=
  ∑ j,a j • (rect K (none:Option J) (some j)+rect K (some j) none)

theorem dir_normal (a : J→K) (p : MvPolynomial (Cells J) K) :
    dir (normal a) p=∑ j,C (a j)*(dir (rect K none (some j)) p+dir (rect K (some j) none) p) := by
  simp [normal,dir_sumv,dir_smulv,dir_addv,smul_eq_mul,mul_add]

@[simp] theorem normal_out (a : J→K) (j : J) : normal a (old (none,some j))=a j := by
  classical
  simp [normal,rect,old,left,right,corner,Finset.sum_apply,Pi.single_apply,mul_ite]

@[simp] theorem normal_in (a : J→K) (j : J) : normal a (old (some j,none))=a j := by
  classical
  simp [normal,rect,old,left,right,corner,Finset.sum_apply,Pi.single_apply,mul_ite]

theorem normal_zero (a : J→K) : atOne (dir (normal a) (permP K J))=0 := by
  simp [dir_normal,atOne_sum,atOne_cmul,atOne_add,rect_zero _ _ (by simp : (none:Option J)≠some _),
    rect_zero _ _ (by simp : some _≠(none:Option J))]

theorem normal_pair (a b : J→K) :
    atOne (dir (normal a) (dir (normal b) (permP K J)))= -8*(∑ j,a j*b j) := by
  rw [dir_normal]
  simp only [atOne_sum,atOne_cmul,atOne_add,permP,rect_pair _ _ (by simp : (none:Option J)≠some _),
    rect_pair _ _ (by simp : some _≠(none:Option J)),normal_in,normal_out,Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  ring

theorem normal_pair_third (a b : J→K) (d : Option J→K) (zd : ∑ i,d i=0) :
    atOne (dir (parameter d) (dir (normal a) (dir (normal b) (permP K J))))=
      ∑ j,4*a j*b j*(d none+d (some j)) := by
  rw [dir_normal a]
  simp only [map_sum,dir_const_mul,map_add,atOne_sum,atOne_cmul,atOne_add,permP,
    rect_pair_third _ _ (by simp : (none:Option J)≠some _) _ d zd,
    rect_pair_third _ _ (by simp : some _≠(none:Option J)) _ d zd,normal_in,normal_out]
  apply sum_congr rfl
  intro j _
  ring

theorem normal_pair_fourth (a b : J→K) (d e : Option J→K) (zd : ∑ i,d i=0) (ze : ∑ i,e i=0) :
    atOne (dir (parameter e) (dir (parameter d) (dir (normal a) (dir (normal b) (permP K J)))))=
      ∑ j,a j*b j*(-8*(d none*e none+d (some j)*e (some j))+8*(∑ i,d i*e i)) := by
  rw [dir_normal a]
  simp only [map_sum,dir_const_mul,map_add,atOne_sum,atOne_cmul,atOne_add,permP,
    rect_pair_fourth _ _ (by simp : (none:Option J)≠some _) _ d e zd ze,
    rect_pair_fourth _ _ (by simp : some _≠(none:Option J)) _ d e zd ze,normal_in,normal_out]
  apply sum_congr rfl
  intro j _
  ring

end PermanentDeformation
