import Quantum.Hadamard.PaleySecond

/-! Paley's type II block formula preserves every simultaneous row-column
permutation of the underlying symmetric conference matrix. -/
noncomputable section
namespace HadamardMod.TorusFrobenius
open Finset

theorem equivariant_second {I:Type} [Fintype I] [DecidableEq I] (C:Conference 0 I)
    (sym:∀i j,C.entry i j=C.entry j i) (e:I ≃ I)
    (inv:∀i j,C.entry (e i) (e j)=C.entry i j) :
    ∃H:RowMatrix 0 (I⊕I), Good H ∧ ∀i j,H ((e.sumCongr e) i) ((e.sumCongr e) j)=H i j := by
  let d (i j:I) : ZMod 0 := if i=j then 1 else 0
  let A (i j:I) := C.entry i j+d i j
  let B (i j:I) := C.entry i j-d i j
  let H : RowMatrix 0 (I⊕I)
    | .inl i,.inl j => A i j
    | .inl i,.inr j => B i j
    | .inr i,.inl j => B i j
    | .inr i,.inr j => -A i j
  have sgn (i j:I) : Sign (A i j) ∧ Sign (B i j) ∧ Sign (-A i j) := by
    by_cases e : i=j
    · subst j; simp [A,B,C.diag,d,Sign]
    · rcases C.sign i j e with h|h <;> simp [A,B,d,e,h,Sign]
  have same (i k:I) (ne:i≠k) : (∑ j,A i j*A k j)+(∑ j,B i j*B k j)=0 := by
    rw [←Finset.sum_add_distrib]
    have pair (j:I) : A i j*A k j+B i j*B k j=2*(C.entry i j*C.entry k j) := by
      have dd : d i j*d k j=0 := by
        by_cases h : i=j
        · subst j; simp [d,Ne.symm ne]
        · simp [d,h]
      dsimp [A,B]
      linear_combination 2*dd
    simp [pair,←Finset.mul_sum,C.off i k ne]
  have mixed (i k:I) : (∑ j,A i j*B k j)-(∑ j,B i j*A k j)=0 := by
    rw [←Finset.sum_sub_distrib]
    have pair (j:I) : A i j*B k j-B i j*A k j=
      2*((if i=j then C.entry k i else 0)-(if k=j then C.entry i k else 0)) := by
      dsimp [A,B,d]
      by_cases h : i=j <;> by_cases e : k=j
      · subst j; subst k; simp <;> ring
      · subst j; simp [e] <;> ring
      · subst j; simp [h] <;> ring
      · simp [h,e] <;> ring
    simp [pair,←Finset.mul_sum,Finset.sum_sub_distrib,sym k i]
  have good : Good H := by
    constructor
    · rintro (i|i) (j|j)
      · exact (sgn i j).1
      · exact (sgn i j).2.1
      · exact (sgn i j).2.1
      · exact (sgn i j).2.2
    · rintro (i|i) (k|k) ne <;> rw [Fintype.sum_sum_type]
      · exact same i k (fun e => ne (congrArg Sum.inl e))
      · simpa only [H,mul_neg,Finset.sum_neg_distrib,←sub_eq_add_neg] using mixed i k
      · simp only [H,neg_mul,Finset.sum_neg_distrib]
        linear_combination -(mixed i k)
      · simp only [H,neg_mul_neg]
        rw [add_comm]
        exact same i k (fun e => ne (congrArg Sum.inr e))
  refine ⟨H,good,?_⟩
  have dInv (i j:I) : d (e i) (e j)=d i j := by simp [d,e.injective.eq_iff]
  have aInv (i j:I) : A (e i) (e j)=A i j := by simp only [A,inv,dInv]
  have bInv (i j:I) : B (e i) (e j)=B i j := by simp only [B,inv,dInv]
  rintro (i|i) (j|j)
  · exact aInv .. 
  · exact bInv ..
  · exact bInv ..
  · exact congrArg (fun x : ZMod 0 => -x) (aInv i j)

variable {F:Type} [Field F] [Fintype F] [DecidableEq F]

def entry : Option F → Option F → ℤ
  | none,none => 0
  | some _,none | none,some _ => 1
  | some i,some j => quadraticChar F (j-i)

/-- The affine chart with its distinguished point at infinity. -/
def conference (hc:ringChar F≠2) : Conference 0 (Option F) where
  entry := entry
  diag i := by cases i <;> simp [entry] <;> rfl
  sign := by
    rintro ( _|i) ( _|k) ne
    · exact (ne rfl).elim
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact quadraticChar_dichotomy (sub_ne_zero.mpr (fun eq : k=i => ne (congrArg some eq.symm)))
  off := by
    have row (i:F) : (∑j,quadraticChar F (j-i))=0 := ((Equiv.subRight i).sum_comp _).trans
      (quadraticChar_sum_zero hc)
    have dot (i k:F) (ne:i≠k) :
        (∑j,quadraticChar F (j-i)*quadraticChar F (j-k))= -1 := by
      have h:=(Equiv.subRight i).sum_comp (fun z:F => quadraticChar F z*quadraticChar F (z+(i-k)))
      change (∑j,quadraticChar F (j-i)*quadraticChar F (j-i+(i-k)))=_ at h
      simp only [show ∀j:F,j-i+(i-k)=j-k by intro j; abel] at h
      exact h.trans (by simpa [sub_ne_zero.mpr ne] using Hadamard.Paley.character_corr hc (i-k))
    rintro ( _|i) ( _|k) ne
    · exact (ne rfl).elim
    · change (∑j:Option F,entry none j*entry (some k) j:ℤ)=0
      simp only [Fintype.sum_option,entry,zero_mul,one_mul,zero_add,row]
    · change (∑j:Option F,entry (some i) j*entry none j:ℤ)=0
      simp only [Fintype.sum_option,entry,mul_zero,mul_one,zero_add,row]
    · have nd : i≠k := fun h => ne (congrArg some h)
      change (∑j:Option F,entry (some i) j*entry (some k) j:ℤ)=0
      simp only [Fintype.sum_option,entry,one_mul,dot i k nd]
      norm_num

theorem conference_sym (hc:ringChar F≠2) (q4:Fintype.card F % 4≠3) :
    ∀ i j,(conference hc).entry i j=(conference hc).entry j i := by
  rintro ( _|i) ( _|j) <;> try rfl
  have minus : quadraticChar F (-1)=1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
      (FiniteField.isSquare_neg_one_iff.mpr q4)
  change quadraticChar F (j-i)=quadraticChar F (i-j)
  rw [show j-i=(-1)*(i-j) by ring,map_mul,minus,one_mul]

theorem conference_equivariant (hc:ringChar F≠2) (f:F ≃+* F) :
    ∀i j,(conference hc).entry (f.toEquiv.optionCongr i) (f.toEquiv.optionCongr j)=
      (conference hc).entry i j := by
  rintro ( _|i) ( _|j) <;> try rfl
  change quadraticChar F (f j - f i) = quadraticChar F (j-i)
  rw [←map_sub]
  by_cases z : j-i=0
  · simp [z]
  · have fz : f (j-i)≠0 := (map_ne_zero_iff f f.injective).mpr z
    have sq : IsSquare (f (j-i)) ↔ IsSquare (j-i) := by
      constructor
      · exact fun h => by simpa using h.map f.symm.toMonoidHom
      · exact fun h => h.map f.toMonoidHom
    by_cases h : IsSquare (j-i)
    · rw [(quadraticChar_one_iff_isSquare fz).mpr (sq.mpr h),(quadraticChar_one_iff_isSquare z).mpr h]
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr (fun e => h (sq.mp e)),
           quadraticChar_neg_one_iff_not_isSquare.mpr h]

end HadamardMod.TorusFrobenius
