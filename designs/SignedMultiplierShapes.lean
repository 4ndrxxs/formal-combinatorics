import SignedCenteredMultiplier

namespace Signed39.Template

open Finset Contraction

variable {p : ℕ} [Fact p.Prime]

theorem square_multiplier_fixed (u : ZMod p→ℤ) (a : ZMod p) (nz:a≠0) (na:a≠1)
    (matchEq:∃(t:ZMod p)(sg:ℤ),(sg=1∨sg= -1) ∧ ∀x,u ((timesEquiv a nz).symm x)=sg*u (x-t)) :
    ∃base:ZMod p,∀i,u (a^2*i+base)=u (i+base) := by
  obtain ⟨t,sg,sign,h⟩:=matchEq
  let base:=t/(a-1)
  have ab : (a-1)*base=t := by dsimp only [base]; exact mul_div_cancel₀ t (sub_ne_zero.mpr na)
  have act (i:ZMod p) : u (i+base)=sg*u (a*i+base) := by
    have e:=h ((timesEquiv a nz) (i+base))
    rw [AddEquiv.symm_apply_apply] at e
    change u (i+base)=sg*u (a*(i+base)-t) at e
    simpa only [show a*(i+base)-t=a*i+base by linear_combination ab] using e
  refine ⟨base,fun i=>?_⟩
  have h1:=act i
  have h2:=act (a*i)
  rw [←mul_assoc,←pow_two] at h2
  rcases sign with rfl|rfl
  · simpa using (h1.trans (congrArg (fun x:ℤ=>1*x) h2)).symm
  · simpa using (h1.trans (congrArg (fun x:ℤ=> -1*x) h2)).symm

def classWord (tag : ZMod p → Bool) {T : Type} (z b c : T) (i : ZMod p) : T :=
  if i=0 then z else if tag i then b else c

theorem classWord_sum (tag : ZMod p→Bool) (d : ℕ)
    (first : (∑i:ZMod p,classWord tag (0:ℤ) 1 0 i)=d)
    (second : (∑i:ZMod p,classWord tag (0:ℤ) 0 1 i)=d) (z b c : ℤ) :
    (∑i:ZMod p,classWord tag z b c i)=z+(d:ℤ)*b+(d:ℤ)*c := by
  have ww (i:ZMod p) : classWord tag z b c i=(if i=0 then z else 0)+b*classWord tag 0 1 0 i+c*classWord tag 0 0 1 i := by
    by_cases h:i=0 <;> by_cases t:tag i=true <;> simp [classWord,h,t]
  simp only [ww,sum_add_distrib,←mul_sum,first,second]
  simp [mul_comm]

theorem classWord_map (tag : ZMod p→Bool) (z b c : ℤ) (F : ℤ→ℤ) (i : ZMod p) :
    F (classWord tag z b c i)=classWord tag (F z) (F b) (F c) i := by
  by_cases h:i=0 <;> by_cases t:tag i=true <;> simp [classWord,h,t]

def listsFor (d : ℕ) (b c : ℤ) : List ℤ :=
  [-((d:ℤ)*(b+c))]++List.replicate d b++List.replicate d c

def twoForms (d R : ℕ) (E : ℤ) : List (List ℤ) := (List.range (2*R+1)).flatMap fun (i:ℕ)=>
  let b:ℤ:=(i:ℤ)-R
  (List.range (2*R+1)).filterMap fun (j:ℕ)=>
    let c:ℤ:=(j:ℤ)-R
    let z := -((d:ℤ)*(b+c))
    if z^2+(d:ℤ)*b^2+(d:ℤ)*c^2=E then some (listsFor d b c) else none

theorem two_forms_complete (u : ZMod p→ℤ) (a rep : ZMod p) (tag : ZMod p→Bool) (d R : ℕ) (E : ℤ)
    (base : ZMod p) (fix : ∀i,u (a^2*i+base)=u (i+base))
    (cover : ∀i:ZMod p,i≠0 → ∃j:Fin p,(a^2)^j.val*(if tag i then 1 else rep)=i)
    (first : (∑i:ZMod p,classWord tag (0:ℤ) 1 0 i)=d)
    (second : (∑i:ZMod p,classWord tag (0:ℤ) 0 1 i)=d)
    (mu : mass u=0) (eu : energy u=E) (bound : E<((R:ℤ)+1)^2) :
    ∃L∈twoForms d R E,∀F:ℤ→ℤ,(∑i:ZMod p,F (u i))=(L.map F).sum := by
  let g:=fun i=>u (i+base)
  have invariant (j:ℕ) (x:ZMod p) : g ((a^2)^j*x)=g x := by
    induction j with
    | zero=>simp
    | succ j ih=>rw [pow_succ']; simp only [mul_assoc]; exact (fix _).trans ih
  let b:=g 1
  let c:=g rep
  let z:=g 0
  have form (i) : g i=classWord tag z b c i := by
    by_cases h:i=0
    · simp [classWord,h,z]
    · obtain ⟨j,eq⟩:=cover i h
      have v:=invariant j.val (if tag i then 1 else rep)
      rw [eq] at v
      cases t:tag i <;> simpa [classWord,h,t,b,c] using v
  have general (F:ℤ→ℤ) : (∑i:ZMod p,F (u i))=F z+(d:ℤ)*F b+(d:ℤ)*F c := by
    calc
      _=∑i:ZMod p,F (g i) := (sum_translate (fun i=>F (u i)) base).symm
      _=∑i:ZMod p,classWord tag (F z) (F b) (F c) i := by simp only [form,classWord_map]
      _=_ := classWord_sum tag d first second _ _ _
  have massEq:=general id
  change mass u=z+(d:ℤ)*b+(d:ℤ)*c at massEq
  have zz : z= -((d:ℤ)*(b+c)) := by rw [mu] at massEq; linear_combination -massEq
  have energyEq:=general (fun x=>x^2)
  change energy u=z^2+(d:ℤ)*b^2+(d:ℤ)*c^2 at energyEq
  have limits (x:ZMod p) : -((R:ℤ))≤g x ∧ g x≤R := by
    have hi:=single_le_sum (s:=univ) (fun i _=>sq_nonneg (u i)) (mem_univ (x+base))
    change (g x)^2≤energy u at hi
    rw [eu] at hi
    constructor
    · by_contra! h; have h1 : 0≤ -g x-(R:ℤ)-1 := by omega
      nlinarith [mul_nonneg h1 (show 0≤ -g x+(R:ℤ)+1 by omega)]
    · by_contra! h; have h1 : 0≤g x-(R:ℤ)-1 := by omega
      nlinarith [mul_nonneg h1 (show 0≤g x+(R:ℤ)+1 by omega)]
  have bl : -(R:ℤ)≤b ∧ b≤R := limits 1
  have cl : -(R:ℤ)≤c ∧ c≤R := limits rep
  let I:=(b+R).toNat
  let J:=(c+R).toNat
  have iv : (I:ℤ)=b+R := Int.toNat_of_nonneg (by omega)
  have jv : (J:ℤ)=c+R := Int.toNat_of_nonneg (by omega)
  have ir : I∈List.range (2*R+1) := List.mem_range.mpr (by omega)
  have jr : J∈List.range (2*R+1) := List.mem_range.mpr (by omega)
  refine ⟨listsFor d b c,?_,?_⟩
  · unfold twoForms
    apply List.mem_flatMap.mpr
    refine ⟨I,ir,List.mem_filterMap.mpr ⟨J,jr,?_⟩⟩
    dsimp only
    rw [iv,jv,add_sub_cancel_right,add_sub_cancel_right,←zz,←energyEq,eu,ite_eq_left rfl]
  · intro F
    rw [general]
    simp [listsFor,List.map_replicate,←zz,add_assoc]

#print axioms two_forms_complete

end Signed39.Template

