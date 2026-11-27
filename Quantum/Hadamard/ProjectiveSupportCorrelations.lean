import Quantum.Hadamard.ProjectiveSplitSupports

/-! Periodic autocorrelations of the four signed incidence sequences in
Momihara, Suda and Xiang, Theorem 4.1. The identity specifies every
within-class Gram entry directly on the multiplicative group of squares. -/

noncomputable section
open Finset

namespace Hadamard.MSXCore

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def incidence (s : F) (i : Bool) (t : F) : ℤ := by
  classical exact if t∈translated s i then 1 else -1

def sumSquares (f : F → ℤ) : ℤ := ∑ x : F, if quadraticChar F x=1 then f x else 0

private theorem inc_char (i : Bool) (a : F) :
    (if quadraticChar F a=cosetSign i then (1:ℤ) else -1)=
       cosetSign i*quadraticChar F a - (if a=0 then 1 else 0) := by
  by_cases h : a=0
  · subst a; cases i <;> norm_num [cosetSign]
  · rcases quadraticChar_dichotomy h with e|e <;> cases i <;> norm_num [e,h,cosetSign]

private theorem incidence_row {s x y : F} (sn : s≠0) (hx : quadraticChar F x=1)
    (hy : quadraticChar F y=1) (i : Bool) :
    incidence s i (x/y)=cosetSign i*quadraticChar F (x/s-y)-(if x=s*y then 1 else 0) := by
  classical
  have yn : y≠0 := by intro h; subst y; simp at hy
  have ratio : quadraticChar F (x/y)=1 := by
    have h := congrArg (quadraticChar F) (show y*(x/y)=x by field_simp)
    simpa only [map_mul,hy,one_mul,hx] using h
  have rescale : quadraticChar F (x/y/s-1)=quadraticChar F (x/s-y) := by
    have h := congrArg (quadraticChar F) (show y*(x/y/s-1)=x/s-y by field_simp)
    simpa only [map_mul,hy,one_mul] using h
  have zero : x/y/s-1=0 ↔ x=s*y := by
    rw [sub_eq_zero,div_eq_iff sn,one_mul,div_eq_iff yn]
  simp only [incidence,mem_translated sn,ratio,true_and]
  rw [inc_char,rescale]
  simp only [zero]

private theorem sum_split {w : F} (hw : quadraticChar F w= -1) (f : F→ℤ) :
    sumSquares f + sumSquares (fun x ↦ f (x/w))=(∑ x,f x)-f 0 := by
  have wn : w≠0 := by intro eq; subst w; simp at hw
  have h := Equiv.sum_comp (Equiv.mulLeft₀ w wn)
    (fun x : F ↦ if quadraticChar F x=1 then f (x/w) else 0)
  change (∑ x, if quadraticChar F (w*x)=1 then f (w*x/w) else 0)=_ at h
  have term (x : F) : (if quadraticChar F (w*x)=1 then f (w*x/w) else 0)=
      (if quadraticChar F x= -1 then f x else 0) := by
    simp only [map_mul,hw,neg_one_mul,show w*x/w=x by field_simp]
    have test : -(quadraticChar F x)=1 ↔ quadraticChar F x= -1 := by omega
    simp only [test]
  simp_rw [term] at h
  unfold sumSquares
  rw [←h,←sum_add_distrib]
  have pair (x : F) :
      (if quadraticChar F x=1 then f x else 0)+(if quadraticChar F x= -1 then f x else 0)=
      f x-(if x=0 then f 0 else 0) := by
    by_cases z : x=0
    · simp [z]
    · rcases quadraticChar_dichotomy z with e|e <;> simp [e,z]
  simp only [pair,sum_sub_distrib]
  simp

/-- Row products for one choice from each of the two columns of four
cyclotomic sets. The choice in the mixed column has no effect. -/
def incidenceGram (w : F) (i j : Bool) (y z : F) : ℤ :=
  sumSquares (fun x ↦ incidence 1 i (x/y)*incidence 1 i (x/z))+
  sumSquares (fun x ↦ incidence w j (x/y)*incidence w j (x/z))

theorem incidence_gram {w y z : F} (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (hw : quadraticChar F w= -1) (hy : quadraticChar F y=1) (hz : quadraticChar F z=1)
    (i j : Bool) :
    incidenceGram w i j y z =
      if y=z then (Fintype.card F:ℤ)-1 else -2-2*cosetSign i*quadraticChar F (z-y) := by
  classical
  have wn : w≠0 := by intro h; subst w; simp at hw
  have hsign (s : F) (l : Bool) (t : F) : incidence s l t * incidence s l t=1 := by
    unfold incidence; split <;> norm_num
  by_cases ne : y=z
  · subst z
    simpa only [incidenceGram,hsign,ite_true,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
      using sum_split hw (fun _ ↦ 1)
  rw [ite_eq_right ne]
  let χ := quadraticChar F
  let f (x : F) := χ (x-y)*χ (x-z)
  have direct (x : F) (hx : χ x=1) :
        incidence 1 i (x/y)*incidence 1 i (x/z)=f x-
        (if x=y then cosetSign i*χ (y-z) else 0)-(if x=z then cosetSign i*χ (z-y) else 0) := by
    rw [incidence_row one_ne_zero hx hy,incidence_row one_ne_zero hx hz]
    simp only [div_one,one_mul]
    unfold f χ
    by_cases e : x=y
    · subst x; cases i <;> simp [ne,cosetSign]
    · by_cases e' : x=z
      · subst x; cases i <;> simp [e,cosetSign]
      · cases i <;> simp [e,e',cosetSign]
  have part1 : sumSquares (fun x ↦ incidence 1 i (x/y)*incidence 1 i (x/z))=
      sumSquares f-cosetSign i*χ (y-z)-cosetSign i*χ (z-y) := by
    unfold sumSquares
    have term (x : F) :
        (if χ x=1 then incidence 1 i (x/y)*incidence 1 i (x/z) else 0)=
        (if χ x=1 then f x else 0)-
        (if x=y then cosetSign i*χ (y-z) else 0)-(if x=z then cosetSign i*χ (z-y) else 0) := by
      by_cases e : χ x=1
      · simp [e,direct x e]
      · have a : x≠y := fun eq ↦ e (eq ▸ hy)
        have b : x≠z := fun eq ↦ e (eq ▸ hz)
        simp [e,a,b]
    change (∑ x,if χ x=1 then _ else _)=_
    simp only [term,sum_sub_distrib]
    simp [χ]
  have part2 : sumSquares (fun x ↦ incidence w j (x/y)*incidence w j (x/z))=
      sumSquares (fun x ↦ f (x/w)) := by
    apply sum_congr rfl
    intro x _
    by_cases h : χ x=1
    · have avoid (a : F) (ha : χ a=1) : x≠w*a := by
        intro eq; subst x; change quadraticChar F (w*a)=1 at h
        simp [map_mul,hw,show quadraticChar F a=1 from ha] at h
      simp only [show quadraticChar F x=1 from h,ite_true,incidence_row wn h hy,
        incidence_row wn h hz,ite_eq_right (avoid y hy),ite_eq_right (avoid z hz),sub_zero]
      cases j <;> simp [f,χ,cosetSign]
    · simp only [ite_eq_right (show quadraticChar F x≠1 from h)]
  have tr := (Equiv.subRight y).sum_comp (fun t:F ↦ χ t*χ (t+(y-z)))
  change (∑ x,χ (x-y)*χ (x-y+(y-z)))=_ at tr
  have plain : ∑ x,f x= -1 := by
    simp only [show ∀ x:F,x-y+(y-z)=x-z by intro x; abel] at tr
    exact tr.trans (by simpa [χ,sub_ne_zero.mpr ne] using Hadamard.Paley.character_corr hc (y-z))
  have minus : χ (-1)=1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
      (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  have zero : f 0=1 := by
    simp only [f,zero_sub]
    rw [show -y=(-1)*y by ring,show -z=(-1)*z by ring,map_mul,map_mul,minus,hy,hz]
    norm_num
  have sym : χ (y-z)=χ (z-y) := by
    rw [show y-z=(-1)*(z-y) by ring,map_mul,minus,one_mul]
  have split := sum_split hw f
  rw [plain,zero] at split
  rw [incidenceGram,part1,part2,sym]
  change _= -2-2*cosetSign i*χ (z-y)
  linarith

#print axioms incidence_gram


/-- The trivial Fourier coefficient of the quadratic difference kernel on squares. -/
theorem square_shift_sum (hc : ringChar F≠2) (q4 : Fintype.card F%4=1) :
    sumSquares (fun x : F ↦ quadraticChar F (x-1))= -1 := by
  let χ := quadraticChar F
  have minus : χ (-1)=1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
      (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  have shifted : ∑ x : F, χ (x-1)=0 :=
    ((Equiv.subRight (1:F)).sum_comp χ).trans (quadraticChar_sum_zero hc)
  have corr : ∑ x : F, χ x*χ (x-1)= -1 := by
    simpa only [χ,sub_eq_add_neg,ite_eq_right (neg_ne_zero.mpr (one_ne_zero : (1:F)≠0)),zero_add] using
      Hadamard.Paley.character_corr hc (-1:F)
  have term (x : F) :
      2*(if χ x=1 then χ (x-1) else 0)=
        χ x*χ (x-1)+χ (x-1)-(if x=0 then 1 else 0) := by
    by_cases eq : x=0
    · subst x; simp [χ,show quadraticChar F (-1)=1 from minus]
    · rcases quadraticChar_dichotomy eq with v|v <;> change χ x=_ at v <;> rw [v] <;> simp [eq]
      ring
  have weighted := sum_congr (s₁:=univ) rfl (fun x _ ↦ term x)
  simp only [sum_sub_distrib,sum_add_distrib,←mul_sum,corr,shifted,add_zero] at weighted
  change (∑ x : F, if χ x=1 then χ (x-1) else 0)= -1
  simp at weighted
  omega

/-- The row sums of the two signed incidence sequences. The second signed
sequence is balanced for each choice of its cyclotomic class. -/
theorem incidence_sums {w : F} (hc : ringChar F≠2) (q4 : Fintype.card F%4=1)
    (hw : quadraticChar F w= -1) (i j : Bool) :
    sumSquares (incidence (1:F) i) = -1-cosetSign i ∧ sumSquares (incidence w j)=0 := by
  let χ := quadraticChar F
  have minus : χ (-1)=1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
      (FiniteField.isSquare_neg_one_iff.mpr (by omega))
  have shifted : ∑ x : F, χ (x-1)=0 :=
    ((Equiv.subRight (1:F)).sum_comp χ).trans (quadraticChar_sum_zero hc)
  have direct := square_shift_sum hc q4
  change sumSquares (fun x : F ↦ χ (x-1))= -1 at direct
  have rest := sum_split hw (fun x : F ↦ χ (x-1))
  simp only [direct,shifted,zero_sub,minus] at rest
  have wn : w≠0 := by intro eq; subst w; simp at hw
  have one : χ 1=1 := map_one _
  have first (x : F) (hx : χ x=1) :
      incidence 1 i x=cosetSign i*χ (x-1)-(if x=1 then 1 else 0) := by
    simpa only [div_one,one_mul] using incidence_row (s:=1) (y:=1) one_ne_zero hx one i
  have other (x : F) (hx : χ x=1) : incidence w j x=cosetSign j*χ (x/w-1) := by
    have ne : x≠w := by intro eq; subst x; change χ w= -1 at hw; omega
    simpa only [div_one,mul_one,ite_eq_right ne,sub_zero] using incidence_row (y:=1) wn hx one j
  constructor
  · have id (x : F) :
        (if χ x=1 then incidence 1 i x else 0)=
        cosetSign i*(if χ x=1 then χ (x-1) else 0)-(if x=1 then 1 else 0) := by
      by_cases hx : χ x=1
      · simp only [hx,ite_true,first x hx]
      · have ne : x≠1 := fun eq ↦ hx (eq ▸ one)
        simp [hx,ne]
    have s := sum_congr (s₁:=univ) rfl (fun x _ ↦ id x)
    simp only [sum_sub_distrib,←mul_sum] at s
    change (∑ x : F, if χ x=1 then incidence 1 i x else 0)=_
    rw [s,show (∑ x : F, if χ x=1 then χ (x-1) else 0)= -1 from direct]
    simp; ring
  · have id (x : F) :
        (if χ x=1 then incidence w j x else 0)=cosetSign j*(if χ x=1 then χ (x/w-1) else 0) := by
      by_cases hx : χ x=1 <;> simp [hx,other x]
    have s := sum_congr (s₁:=univ) rfl (fun x _ ↦ id x)
    simp only [←mul_sum] at s
    have total : (∑ x : F, if χ x=1 then χ (x/w-1) else 0)=0 := by
      change -1+(∑ x : F, if χ x=1 then χ (x/w-1) else 0)=0-1 at rest
      omega
    change (∑ x : F, if χ x=1 then incidence w j x else 0)=_
    rw [s,total,mul_zero]

#print axioms square_shift_sum
#print axioms incidence_sums

end Hadamard.MSXCore
