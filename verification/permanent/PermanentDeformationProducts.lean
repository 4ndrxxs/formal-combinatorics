import PermanentDeformationFamily
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder PermanentJets
namespace PermanentDeformation
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem prod_jets (s : Finset I) (d e : I→K) :
    eval (fun _ ↦ 1) (monomialOn K s)=1 ∧
    eval (fun _ ↦ 1) (dir d (monomialOn K s))=∑ i ∈ s,d i ∧
    eval (fun _ ↦ 1) (dir e (monomialOn K s))=∑ i ∈ s,e i ∧
    eval (fun _ ↦ 1) (dir e (dir d (monomialOn K s)))=
      (∑ i ∈ s,d i)*(∑ i ∈ s,e i)-∑ i ∈ s,d i*e i := by
  induction s using Finset.induction_on with
  | empty => simp [monomialOn]
  | insert a s ha ih =>
    obtain ⟨h0,hd,he,h2⟩ := ih
    have insert : monomialOn K (insert a s)=X a*monomialOn K s := Finset.prod_insert ha
    rw [insert]
    simp [Derivation.leibniz,smul_eq_mul,h0,hd,he,h2,ha]
    ring_nf
    simp

theorem zero_erase (d : I→K) (zero : ∑ i,d i=0) (a : I) : ∑ i ∈ univ.erase a,d i= -d a := by
  have h := Finset.add_sum_erase univ d (Finset.mem_univ a)
  rw [zero] at h
  linear_combination h

theorem missing_jets (d e : I→K) (zd : ∑ i,d i=0) (ze : ∑ i,e i=0) (a : I) :
    eval (fun _ ↦ 1) (dir d (missing K a))= -d a ∧
    eval (fun _ ↦ 1) (dir e (dir d (missing K a)))=2*(d a*e a)-∑ i,d i*e i := by
  obtain ⟨_,hd,_,h2⟩ := prod_jets (univ.erase a) d e
  have diag := Finset.add_sum_erase univ (fun i ↦ d i*e i) (mem_univ a)
  refine ⟨hd.trans (zero_erase d zd a),?_⟩
  change eval _ (dir e (dir d (monomialOn K _)))=_
  rw [h2,zero_erase d zd a,zero_erase e ze a]
  linear_combination -diag

theorem full_jets (d e : I→K) (zd : ∑ i,d i=0) (ze : ∑ i,e i=0) :
    eval (fun _ ↦ 1) (dir d (full K I))=0 ∧
    eval (fun _ ↦ 1) (dir e (dir d (full K I)))= -(∑ i,d i*e i) := by
  obtain ⟨_,hd,_,h2⟩ := prod_jets univ d e
  exact ⟨hd.trans zd,by simpa [full,monomialOn,zd,ze] using h2⟩

def atOne (p : MvPolynomial (Bigger I) K) := eval (PermanentArrow.point K (none:Option I)) p

theorem atOne_lift (p : MvPolynomial (Bigger I) K) : eval (fun _ ↦ 1) (lift p)=atOne p := by
  rw [eval_lift,parameter_one,atOne]

@[simp] theorem dir_two {T : Type*} [Fintype T] (w : T→K) : dir w (2:MvPolynomial T K)=0 := by
  rw [←map_ofNat (C : K→+*MvPolynomial T K) 2]
  exact dir_C w 2

theorem rect_third (i j : I) (ij : i≠j) (v : Bigger I) (d : I→K) (zd : ∑ i,d i=0) :
    atOne (dir (parameter d) (dir (rect K i j) (pderiv v (per K (Option I)))))=
      if v=old (j,i) then 2*(d i+d j) else 0 := by
  let p := dir (rect K i j) (pderiv v (per K (Option I)))
  have h := congrArg (fun q : MvPolynomial I K ↦ eval (fun _ ↦ 1) (dir d q))
    (universal_laws (K:=K) i j ij v).2.2
  change eval _ (dir d (lift p))=_ at h
  rw [lift_dir,atOne_lift] at h
  change atOne (dir (parameter d) p)=_
  rw [h]
  by_cases hit : v=old (j,i)
  · simp only [hit,ite_true]
    simp [Derivation.leibniz,smul_eq_mul,(missing_jets d d zd zd i).1,(missing_jets d d zd zd j).1]
    ring
  · simp [hit]

theorem rect_fourth (i j : I) (ij : i≠j) (v : Bigger I) (d e : I→K)
    (zd : ∑ i,d i=0) (ze : ∑ i,e i=0) :
    atOne (dir (parameter e) (dir (parameter d) (dir (rect K i j) (pderiv v (per K (Option I))))))=
      if v=old (j,i) then -4*(d i*e i+d j*e j)+4*(∑ k,d k*e k) else 0 := by
  let p := dir (rect K i j) (pderiv v (per K (Option I)))
  have h := congrArg (fun q : MvPolynomial I K ↦ eval (fun _ ↦ 1) (dir e (dir d q)))
    (universal_laws (K:=K) i j ij v).2.2
  change eval _ (dir e (dir d (lift p)))=_ at h
  rw [lift_dir,lift_dir,atOne_lift] at h
  change atOne (dir (parameter e) (dir (parameter d) p))=_
  rw [h]
  by_cases hit : v=old (j,i)
  · simp only [hit,ite_true]
    simp [Derivation.leibniz,smul_eq_mul,(missing_jets d e zd ze i).2,(missing_jets d e zd ze j).2]
    ring
  · simp [hit]

theorem corner_third (i j : I) (ij : i≠j) (d e : I→K) (zd : ∑ i,d i=0) (ze : ∑ i,e i=0) :
    atOne (dir (parameter e) (dir (parameter d) (pderiv corner (per K (Option I)))))=
      -(∑ k,d k*e k) := by
  have h := congrArg (fun q : MvPolynomial I K ↦ eval (fun _ ↦ 1) (dir e (dir d q)))
    (universal_laws (K:=K) i j ij corner).1
  change eval _ (dir e (dir d (lift _)))=_ at h
  rw [lift_dir,lift_dir,atOne_lift] at h
  exact h.trans (full_jets d e zd ze).2

end PermanentDeformation
