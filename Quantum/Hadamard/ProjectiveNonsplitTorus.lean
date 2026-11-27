import Quantum.Hadamard.ProjectivePaleyAction
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-! The odd norm-one subgroup of a nonsplit quadratic field and its
projective Paley coordinates. -/

noncomputable section
open Finset Matrix
open Hadamard.ProjectiveSigning.Coordinates
namespace Hadamard.NonsplitTorus

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

abbrev Ext (d : F) := QuadraticAlgebra F d 0

private noncomputable local instance (d : F) : Fintype (Ext d) :=
  Fintype.ofEquiv (F×F) (QuadraticAlgebra.equivProd d 0).symm

theorem norm_one_generator (d : F) [Fact (¬ IsSquare d)] (q4 : Fintype.card F%4=1)
    (lo : 5≤Fintype.card F) : ∃ h : (Ext d)ˣ,
    orderOf h=(Fintype.card F+1)/2 ∧ ((h:Ext d).norm)=1 := by
  let t := Fintype.card F/4
  have size : Fintype.card F=4*t+1 := by dsimp [t]; omega
  have tt : 0<t := by omega
  have c : Fintype.card (Ext d)= (Fintype.card F)^2 := by
    simpa only [Fintype.card_prod,pow_two] using Fintype.card_congr (QuadraticAlgebra.equivProd d 0)
  obtain ⟨g,hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic (Ext d)ˣ)
  have full : orderOf g=(8*t)*(2*t+1) := by
    rw [hg,Nat.card_eq_fintype_card,Fintype.card_units,c,size,
      show (4*t+1)^2=(8*t)*(2*t+1)+1 by ring,Nat.add_sub_cancel]
  refine ⟨g^(8*t),?_,?_⟩
  · rw [orderOf_pow_of_dvd (by omega) (by rw [full]; exact dvd_mul_right ..),full]
    rw [Nat.mul_div_cancel_left _ (by omega : 0<8*t)]
    omega
  · change QuadraticAlgebra.norm ((g:Ext d)^(8*t))=1
    rw [map_pow,show 8*t=(4*t)*2 by ring,pow_mul]
    have nz : (g:Ext d).norm≠0 := fun h ↦ g.ne_zero (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h)
    have eq := FiniteField.pow_card_sub_one_eq_one _ nz
    rw [size,Nat.add_sub_cancel] at eq
    rw [eq,one_pow]

#print axioms norm_one_generator


variable {d : F} [Fact (¬ IsSquare d)]

omit [Fintype F] [Fact (¬ IsSquare d)] in
private theorem scale_nonzero (z : Ext d) (hz : z≠0) : scale z.re z.im≠0 := by
  apply scale_ne
  by_contra! bad
  exact hz (QuadraticAlgebra.ext bad.1 bad.2)

omit [Fintype F] [Fact (¬ IsSquare d)] in
/-- Two nonzero vectors with the same projective point differ by a field scalar. -/
theorem scalar_of_point_eq {z w : Ext d} (hz : z≠0) (hw : w≠0)
    (eq : point z.re z.im = point w.re w.im) :
    ∃ r : F, r≠0 ∧ z=algebraMap F (Ext d) r*w := by
  let s := scale z.re z.im
  let t := scale w.re w.im
  have tn : t≠0 := scale_nonzero w hw
  have sn : s≠0 := scale_nonzero z hz
  let r := s/t
  have rt : r*t=s := div_mul_cancel₀ s tn
  refine ⟨r,div_ne_zero sn tn,?_⟩
  have cx : s*x (point w.re w.im)=z.re := by rw [←eq]; exact restoreX ..
  have cy : s*y (point w.re w.im)=z.im := by rw [←eq]; exact restoreY ..
  have kx : t*x (point w.re w.im)=w.re := restoreX ..
  have ky : t*y (point w.re w.im)=w.im := restoreY ..
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      zero_mul,mul_zero,add_zero]
    exact cx.symm.trans ((by rw [←mul_assoc, rt] : s*x (point w.re w.im)=r*(t*x (point w.re w.im))).trans (congrArg (r*·) kx))
  · simp only [QuadraticAlgebra.im_mul,QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      zero_mul,mul_zero,add_zero]
    exact cy.symm.trans ((by rw [←mul_assoc, rt] : s*y (point w.re w.im)=r*(t*y (point w.re w.im))).trans (congrArg (r*·) ky))

def spin (h : (Ext d)ˣ) (i : Fin (orderOf h)) : Ext d := (h:Ext d)^i.val

def offset (d : F) (b : Bool) : Ext d := if b then ⟨0,1⟩ else 1

omit [Fintype F] [DecidableEq F] [Fact (¬ IsSquare d)] in
private theorem offset_ne (b : Bool) : offset d b ≠ 0 := by
  cases b
  · simp [offset]
  · intro h
    have u := congrArg QuadraticAlgebra.im h
    change (1:F)=0 at u
    exact one_ne_zero u

omit [Fintype F] [DecidableEq F] [Fact (¬ IsSquare d)] in
private theorem offset_norm (b : Bool) : (offset d b).norm=if b then -d else 1 := by
  cases b
  · exact QuadraticAlgebra.norm_one
  · simp [offset,QuadraticAlgebra.norm_def]

def vector (h : (Ext d)ˣ) (i : Bool×Fin (orderOf h)) : Ext d :=
  offset d i.1 * spin h i.2

omit [Fintype F] [DecidableEq F] [Fact (¬ IsSquare d)] in
private theorem spin_norm (h : (Ext d)ˣ) (hn : (h:Ext d).norm=1) (i : Fin (orderOf h)) :
    (spin h i).norm=1 := by simp [spin,hn]

omit [Fintype F] [DecidableEq F] [Fact (¬ IsSquare d)] in
private theorem spin_period (h : (Ext d)ˣ) (i : Fin (orderOf h)) :
    (spin h i)^(orderOf h)=1 := by
  have p : (h : Ext d) ^ orderOf h=1 := by
    simpa only [Units.val_pow_eq_pow_val,Units.val_one] using congrArg Units.val (pow_orderOf_eq_one h)
  simp [spin,pow_right_comm (h:Ext d) i.val (orderOf h),p]

private theorem offset_character (d : F) [Fact (¬ IsSquare d)] (hm : quadraticChar F (-1)=1) (b : Bool) :
    quadraticChar F (offset d b).norm=(if b then -1 else 1) := by
  have ns : quadraticChar F d= -1 := quadraticChar_neg_one_iff_not_isSquare.mpr Fact.out
  cases b <;> simp only [offset_norm,Bool.false_eq_true,ite_false,ite_true,map_one]
  rw [show -d=(-1)*d by ring,map_mul,hm,ns,one_mul]

/-- The two norm classes give disjoint projective orbits, and each orbit
contains one point for each power of the odd-order generator. -/
theorem projective_chart_bijective (q4 : Fintype.card F%4=1) (hm : quadraticChar F (-1)=1)
    (h : (Ext d)ˣ) (ho : orderOf h=(Fintype.card F+1)/2) (hn : (h:Ext d).norm=1) :
    Function.Bijective (fun i ↦ point (vector h i).re (vector h i).im) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨b,i⟩ ⟨c,j⟩ equal
    have nonzero (s : Bool) (k : Fin (orderOf h)) : vector h (s,k)≠0 :=
      mul_ne_zero (offset_ne s) (pow_ne_zero _ h.ne_zero)
    obtain ⟨r,rn,rel⟩ := scalar_of_point_eq (nonzero b i) (nonzero c j) equal
    have nr := congrArg QuadraticAlgebra.norm rel
    simp only [vector,map_mul,QuadraticAlgebra.norm_algebraMap,spin_norm h hn,mul_one] at nr
    have ch := congrArg (quadraticChar F) nr
    simp only [map_mul,map_pow,quadraticChar_sq_one rn,one_mul,offset_character d hm] at ch
    have same : b=c := by cases b <;> cases c <;> simp_all
    subst c
    have rel' : spin h i=algebraMap F (Ext d) r*spin h j := by
      apply mul_left_cancel₀ (offset_ne (d:=d) b)
      simpa only [vector,mul_left_comm] using rel
    have sq := congrArg QuadraticAlgebra.norm rel'
    simp only [map_mul,QuadraticAlgebra.norm_algebraMap,spin_norm h hn,mul_one] at sq
    have periodic := congrArg (fun z : Ext d ↦ z^(orderOf h)) rel'
    simp only [mul_pow,spin_period,mul_one] at periodic
    have odd : Odd (orderOf h) := ⟨Fintype.card F/4,by omega⟩
    have scalar : algebraMap F (Ext d) r=1 := by
      rcases sq_eq_one_iff.mp sq.symm with a|a
      · rw [a,map_one]
      · simpa [a,odd.neg_one_pow] using periodic.symm
    rw [scalar,one_mul] at rel'
    have un : h^i.val=h^j.val := Units.ext (by simpa only [Units.val_pow_eq_pow_val,spin] using rel')
    have ij := Fin.ext (pow_injOn_Iio_orderOf (x:=h) i.isLt j.isLt un)
    rw [ij]
  · simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Fintype.card_option,ho]
    omega

#print axioms projective_chart_bijective


omit [Fintype F] [DecidableEq F] [Fact (¬ IsSquare d)] in
private theorem spin_add (h : (Ext d)ˣ) [NeZero (orderOf h)] (i j : Fin (orderOf h)) :
    spin h (i+j)=spin h i*spin h j := by
  have t : h^(i+j).val=h^i.val*h^j.val := by rw [Fin.val_add,pow_mod_orderOf,pow_add]
  simpa only [Units.val_pow_eq_pow_val,Units.val_mul,spin] using congrArg Units.val t

def wedge (z w : Ext d) : F := z.im*w.re-z.re*w.im

omit [Fintype F] [DecidableEq F] [Fact (¬ IsSquare d)] in
private theorem wedge_offsets (z w : Ext d) (hn : z.norm=1) (a b : Bool) :
    wedge (offset d a*z) (offset d b*(z*w)) =
      if a then (if b then d*w.im else w.re) else (if b then -w.re else -w.im) := by
  simp only [QuadraticAlgebra.norm_def,zero_mul,add_zero] at hn
  cases a <;> cases b <;> simp [offset,wedge,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
  · linear_combination -w.im*hn
  · linear_combination -w.re*hn
  · linear_combination w.re*hn
  · linear_combination d*w.im*hn

/-- The first diagonal block has sequence χ(im hᵗ), the other has its
negative, and both off-diagonal blocks have sequence χ(re hᵗ). -/
def cyclicEntry (h : (Ext d)ˣ) [NeZero (orderOf h)] (i j : Bool×Fin (orderOf h)) : ℤ :=
  let w := spin h (j.2-i.2)
  if i.1 then (if j.1 then -quadraticChar F w.im else quadraticChar F w.re)
  else (if j.1 then quadraticChar F w.re else quadraticChar F w.im)

theorem cyclic_wedge (hm : quadraticChar F (-1)=1) (h : (Ext d)ˣ) [NeZero (orderOf h)]
    (hn : (h:Ext d).norm=1) (i j : Bool×Fin (orderOf h)) :
    quadraticChar F (wedge (vector h i) (vector h j))=cyclicEntry h i j := by
  have diff : spin h i.2*spin h (j.2-i.2)=spin h j.2 := by
    rw [mul_comm,←spin_add,sub_add_cancel]
  change quadraticChar F (wedge (offset d i.1*spin h i.2) (offset d j.1*spin h j.2))=_
  rw [←diff,wedge_offsets _ _ (spin_norm h hn _)]
  have ns : quadraticChar F d= -1 := quadraticChar_neg_one_iff_not_isSquare.mpr Fact.out
  have flip (v:F) : quadraticChar F (-v)=quadraticChar F v := by rw [←neg_one_mul v,map_mul,hm,one_mul]
  rcases i with ⟨a,k⟩; rcases j with ⟨b,l⟩
  cases a <;> cases b <;> simp [cyclicEntry,flip,map_mul,ns]

omit [Fact (¬ IsSquare d)] in
private theorem wedge_chart (hm : quadraticChar F (-1)=1) (z w : Ext d) :
    quadraticChar F (wedge z w)=quadraticChar F (scale z.re z.im)*quadraticChar F (scale w.re w.im)*
      HadamardMod.TorusFrobenius.entry (point z.re z.im) (point w.re w.im) := by
  have eq : scale z.re z.im * scale w.re w.im * bracket (point z.re z.im) (point w.re w.im)=wedge z w := by
    calc
      _ = (scale z.re z.im*y (point z.re z.im))*(scale w.re w.im*x (point w.re w.im))-
          (scale z.re z.im*x (point z.re z.im))*(scale w.re w.im*y (point w.re w.im)) := by unfold bracket; ring
      _ = _ := by rw [restoreY,restoreX,restoreX,restoreY]; rfl
  rw [←eq,map_mul,map_mul,char_bracket hm]

def normAt (d : F) (p : Option F) : F := (x p)^2-d*(y p)^2

omit [Fact (¬ IsSquare d)] in
private theorem norm_chart (z : Ext d) (hz : z≠0) :
    quadraticChar F (normAt d (point z.re z.im))=quadraticChar F z.norm := by
  let s := scale z.re z.im
  let p := point z.re z.im
  have e : s^2*normAt d p=z.norm := by
    calc
      _ = (s*x p)^2-d*(s*y p)^2 := by unfold normAt; ring
      _ = _ := by rw [show s*x p=z.re from restoreX ..,show s*y p=z.im from restoreY ..]
                  simp [QuadraticAlgebra.norm_def,pow_two,mul_assoc]
  have eq := congrArg (quadraticChar F) e
  simpa only [map_mul,map_pow,quadraticChar_sq_one (scale_nonzero z hz),one_mul,s,p] using eq

def twoCirculant (h : (Ext d)ˣ) [NeZero (orderOf h)] (α : ℤ) :
    Matrix (Bool×Fin (orderOf h)) (Bool×Fin (orderOf h)) ℝ :=
  Matrix.of (fun i j ↦ (cyclicEntry h i j : ℝ)) + diagonal (fun i : Bool×Fin (orderOf h) ↦ if i.1 then -(α:ℝ) else (α:ℝ))

theorem two_circulant_det (q4 : Fintype.card F%4=1) (hm : quadraticChar F (-1)=1)
    (h : (Ext d)ˣ) [NeZero (orderOf h)] (ho : orderOf h=(Fintype.card F+1)/2)
    (hn : (h:Ext d).norm=1) (α : ℤ) :
    |(twoCirculant h α).det|=Hadamard.ProjectiveSigning.signedDet (fun p ↦ α*quadraticChar F (normAt d p)) := by
  let E := Equiv.ofBijective _ (projective_chart_bijective q4 hm h ho hn)
  let U (i : Bool×Fin (orderOf h)) : ℝ := (quadraticChar F (scale (vector h i).re (vector h i).im) : ℤ)
  let s (p : Option F) : ℝ := ((α*quadraticChar F (normAt d p):ℤ):ℝ)
  let A := Hadamard.ProjectiveSigning.realPaley (F:=F)+diagonal s
  have nz (i : Bool×Fin (orderOf h)) : vector h i≠0 :=
    mul_ne_zero (offset_ne i.1) (pow_ne_zero _ h.ne_zero)
  have us (i) : U i=1 ∨ U i= -1 := by
    dsimp [U]; exact_mod_cast quadraticChar_dichotomy (scale_nonzero _ (nz i))
  have ent (i j) : (cyclicEntry h i j : ℝ)=U i*U j*Hadamard.ProjectiveSigning.realPaley (E i) (E j) := by
    have z := (cyclic_wedge hm h hn i j).symm.trans (wedge_chart hm (vector h i) (vector h j))
    dsimp [U,E,Hadamard.ProjectiveSigning.realPaley]
    exact_mod_cast z
  have sign (i) : s (E i)=(if i.1 then -(α:ℝ) else (α:ℝ)) := by
    change ((α*quadraticChar F (normAt d (point (vector h i).re (vector h i).im)):ℤ):ℝ)=_
    rw [norm_chart _ (nz i)]
    simp only [vector,map_mul,spin_norm h hn,mul_one,offset_character d hm]
    rcases i with ⟨b,k⟩; cases b <;> simp
  have eqn : twoCirculant h α=diagonal U * (A.submatrix E E) *diagonal U := by
    ext i j
    simp only [twoCirculant,A,Matrix.add_apply,Matrix.diagonal_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,
      Matrix.submatrix_apply,Equiv.apply_eq_iff_eq]
    change (cyclicEntry h i j:ℝ)+(if i=j then _ else 0)=_
    rw [ent]
    by_cases e : i=j
    · subst j; simp only [ite_true,sign]
      rcases us i with hi|hi <;> rw [hi] <;> ring
    · simp [e]; ring
  have invariant := Hadamard.ProjectiveSigning.abs_det_signed (A.submatrix E E) U 1
    (by intro i; rcases us i with hi|hi <;> simp [hi]) (by norm_num)
  simpa only [one_smul,←eqn,Matrix.det_submatrix_equiv_self,A,s,Hadamard.ProjectiveSigning.signedDet] using invariant

#print axioms cyclic_wedge
#print axioms two_circulant_det


def firstSeq (h : (Ext d)ˣ) [NeZero (orderOf h)] (α : ℤ) (t : Fin (orderOf h)) : ℤ :=
  if t=0 then α else quadraticChar F (spin h t).im

def secondSeq (h : (Ext d)ˣ) (t : Fin (orderOf h)) : ℤ := quadraticChar F (spin h t).re

theorem symmetric_sequences (hm : quadraticChar F (-1)=1) (h : (Ext d)ˣ) [NeZero (orderOf h)]
    (hn : (h:Ext d).norm=1) (α : ℤ) (t : Fin (orderOf h)) :
    firstSeq h α (-t)=firstSeq h α t ∧ secondSeq h (-t)=secondSeq h t := by
  have inv : spin h (-t)=star (spin h t) := by
    apply mul_left_cancel₀ (pow_ne_zero _ h.ne_zero : spin h t≠0)
    change spin h t*spin h (-t)=spin h t*star (spin h t)
    rw [←spin_add,add_neg_cancel,←QuadraticAlgebra.algebraMap_norm_eq_mul_star,spin_norm h hn,map_one]
    simp [spin]
  have flip (v : F) : quadraticChar F (-v)=quadraticChar F v := by rw [←neg_one_mul v,map_mul,hm,one_mul]
  simp only [firstSeq,secondSeq,inv,QuadraticAlgebra.re_star,QuadraticAlgebra.im_star,neg_eq_zero,
    zero_mul,add_zero,flip,and_self]

omit [Fact (¬IsSquare d)] in
/-- This is the literal signed block matrix [[A,B],[B,-A]], with both
sequences indexed by the difference of the column and row indices. -/
theorem two_circulant_entries (h : (Ext d)ˣ) [NeZero (orderOf h)] (α : ℤ)
    (a b : Bool) (k l : Fin (orderOf h)) :
    twoCirculant h α (a,k) (b,l) =
      ((if a=b then (if a then -firstSeq h α (l-k) else firstSeq h α (l-k))
        else secondSeq h (l-k) : ℤ):ℝ) := by
  by_cases e : k=l
  · subst l
    cases a <;> cases b <;> simp [twoCirculant,cyclicEntry,firstSeq,secondSeq,spin,
      show (1:Ext d).im=0 from rfl]
  · have ne : l-k≠0 := sub_ne_zero.mpr (Ne.symm e)
    cases a <;> cases b <;> simp [twoCirculant,cyclicEntry,firstSeq,secondSeq,e,ne]

#print axioms symmetric_sequences
#print axioms two_circulant_entries


/-- Every entry of the completed two-circulant matrix is a genuine sign. -/
theorem sign_entries (q4 : Fintype.card F%4=1) (hm : quadraticChar F (-1)=1)
    (h : (Ext d)ˣ) [NeZero (orderOf h)] (ho : orderOf h=(Fintype.card F+1)/2)
    (hn : (h:Ext d).norm=1) (α : ℤ) (unit : α^2=1) (i j : Bool×Fin (orderOf h)) :
    twoCirculant h α i j=1 ∨ twoCirculant h α i j= -1 := by
  by_cases same : i=j
  · subst j
    rcases i with ⟨a,k⟩
    rw [two_circulant_entries]
    rcases sq_eq_one_iff.mp unit with e|e <;> cases a <;> simp [firstSeq,e]
  · have hc : ringChar F≠2 := by
      intro eq; have even := FiniteField.even_card_of_char_two eq; omega
    let E := fun z : Bool×Fin (orderOf h) ↦ point (vector h z).re (vector h z).im
    have distinct : E i≠E j := (projective_chart_bijective q4 hm h ho hn).1.ne same
    have sig := (HadamardMod.TorusFrobenius.conference (F:=F) hc).sign (E i) (E j) distinct
    change HadamardMod.TorusFrobenius.entry (E i) (E j)=1 ∨ HadamardMod.TorusFrobenius.entry (E i) (E j)= -1 at sig
    have nz (k : Bool×Fin (orderOf h)) : vector h k≠0 :=
      mul_ne_zero (offset_ne k.1) (pow_ne_zero _ h.ne_zero)
    let u (k : Bool×Fin (orderOf h)) := quadraticChar F (scale (vector h k).re (vector h k).im)
    have us (k) : u k=1 ∨ u k= -1 := quadraticChar_dichotomy (scale_nonzero _ (nz k))
    have eq : cyclicEntry h i j=u i*u j*HadamardMod.TorusFrobenius.entry (E i) (E j) :=
      (cyclic_wedge hm h hn i j).symm.trans (wedge_chart hm _ _)
    have bound : cyclicEntry h i j=1 ∨ cyclicEntry h i j= -1 := by
      rw [eq]; rcases us i with a|a <;> rcases us j with b|b <;> rcases sig with c|c <;> norm_num [a,b,c]
    simp only [twoCirculant,Matrix.add_apply,Matrix.of_apply,Matrix.diagonal_apply,ite_eq_right same,add_zero]
    exact_mod_cast bound

#print axioms sign_entries

end Hadamard.NonsplitTorus
