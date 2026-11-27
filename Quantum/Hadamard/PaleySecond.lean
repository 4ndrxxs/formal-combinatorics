import Quantum.Hadamard.Conference

/-! Paley type II. A symmetric zero-diagonal conference matrix produces
an ordinary Hadamard matrix of twice its order. -/
noncomputable section
namespace HadamardMod
open Finset
variable {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

theorem second_of_conference (C : Conference m I) (sym : ∀ i j,C.entry i j=C.entry j i) :
    AtOrder m (2*Fintype.card I) := by
  let d (i j:I) : ZMod m := if i=j then 1 else 0
  let A (i j:I) := C.entry i j+d i j
  let B (i j:I) := C.entry i j-d i j
  let H : RowMatrix m (I⊕I)
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
  exact of_card good (by simp [two_mul])

theorem paley_second (m q : ℕ) [Fact q.Prime] (hq : q%4=1) :
    AtOrder m (2*(q+1)) := by
  let C := paleyConference m q (by omega)
  have sym (i j : Option (ZMod q)) : C.entry i j=C.entry j i := by
    cases i <;> cases j <;> try rfl
    rename_i i j
    change (Hadamard.Paley.Q q i j:ZMod m)=(Hadamard.Paley.Q q j i:ZMod m)
    have hn : quadraticChar (ZMod q) (-1)=1 :=
      (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr one_ne_zero)).mpr
      (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega))
    unfold Hadamard.Paley.Q
    rw [show j-i=(-1)*(i-j) by ring,map_mul,hn,one_mul]
  simpa using second_of_conference C sym

#print axioms paley_second
end HadamardMod
