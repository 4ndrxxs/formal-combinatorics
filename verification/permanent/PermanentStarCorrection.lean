import PermanentStarPairings
import PermanentArrowRank

/-! The corrected second derivative on the radical is the Laplacian of a star. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder PermanentJets PermanentCurve
namespace PermanentDeformation
variable {K J : Type*} [Field K] [Fintype J] [DecidableEq J]
abbrev base (K J : Type*) [Field K] [Fintype J] [DecidableEq J] : Cells J→K :=
  PermanentArrow.point K (none:Option (Option J))

def direction (K J : Type*) [Field K] [Fintype J] [DecidableEq J] : Cells J→K := normal (fun _ ↦ 1)
def correction (d : Option J→K) : Cells J→K := normal (fun j ↦ (d none+d (some j))/2)
def bend (K J : Type*) [Field K] [Fintype J] [DecidableEq J] : Cells J→K :=
  (4*(Fintype.card J:K)) • Pi.single corner 1

theorem parameter_kernel (d : Option J→K) (zd : ∑ i,d i=0) (v : Cells J) :
    atOne (dir (parameter d) (pderiv v (permP K J)))=0 := by
  have he : hessian (permP K J) (base K J)=PermanentArrow.model K (Option J) := by
    ext u w
    exact (PermanentArrow.all_entries K (none:Option (Option J)) u w).2.2
  have eq : parameter d=PermanentArrow.diagonalLift d := by
    funext ⟨a,b⟩
    cases a <;> cases b <;> simp [parameter,PermanentArrow.diagonalLift,zd]
  change eval (base K J) _=0
  rw [dir_hessian,he,eq,PermanentArrow.image_lift,zd,zero_smul,Pi.zero_apply]

theorem cancel_first (two : (2:K)≠0) (d : Option J→K) (zd : ∑ i,d i=0) (v : Cells J) :
    atOne (dir (direction K J) (dir (parameter d) (pderiv v (permP K J))))+
      atOne (dir (correction d) (pderiv v (permP K J)))=0 := by
  rw [dir_comm (direction K J) (parameter d)]
  unfold direction correction
  rw [dir_normal,dir_normal]
  simp only [map_sum,dir_const_mul,map_add,atOne_sum,atOne_cmul,atOne_add,permP,
    rect_third _ _ (by simp : (none:Option J)≠some _) _ d zd,
    rect_third _ _ (by simp : some _≠(none:Option J)) _ d zd,
    rect_row _ _ (by simp : (none:Option J)≠some _),rect_row _ _ (by simp : some _≠(none:Option J)),
    ←Finset.sum_add_distrib]
  apply sum_eq_zero
  intro j _
  split_ifs <;> field_simp <;> ring

theorem corner_bend [Nonempty J] (d e : Option J→K) (zd : ∑ i,d i=0) (ze : ∑ i,e i=0) :
    atOne (dir (parameter e) (dir (parameter d) (dir (bend K J) (permP K J))))=
      -(4*(Fintype.card J:K))*(∑ i,d i*e i) := by
  obtain ⟨j⟩ := ‹Nonempty J›
  simp only [bend,dir_smulv,smul_apply,smul_eq_mul,dir_single,dir_const_mul,atOne_cmul,permP,
    corner_third (none:Option J) (some j) (by simp) d e zd ze]
  ring

theorem corrected_second [Nonempty J] (two : (2:K)≠0) (d e : Option J→K)
    (zd : ∑ i,d i=0) (ze : ∑ i,e i=0) :
    atOne (dir (parameter e) (dir (parameter d) (dir (direction K J) (dir (direction K J) (permP K J)))))+
      2*atOne (dir (parameter e) (dir (parameter d) (dir (bend K J) (permP K J))))+
      2*atOne (dir (parameter e) (dir (direction K J) (dir (correction d) (permP K J))))=
      -4*(∑ j,(d none-d (some j))*(e none-e (some j))) := by
  rw [corner_bend d e zd ze]
  unfold direction correction
  rw [normal_pair_fourth _ _ d e zd ze,normal_pair_third _ _ e ze]
  have c : (Fintype.card J:K)*(8*(∑ i,d i*e i))=∑ _ : J,8*(∑ i,d i*e i) := by simp
  have neg : 2*(-(4*(Fintype.card J:K))*(∑ i,d i*e i))= -(∑ _ : J,8*(∑ i,d i*e i)) := by
    rw [←c]
    ring
  rw [neg,←Finset.sum_neg_distrib,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  field_simp
  ring

end PermanentDeformation
