import Quantum.Hadamard.Extension

/-! Lexicographic products of skew Paley cores give modular extension
matrices with two exact inner products whose difference is the order minus one. -/
noncomputable section
namespace HadamardMod
open Finset
variable {m : ℕ} {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

structure SkewCore (m : ℕ) (I : Type*) [Fintype I] [DecidableEq I] where
  entry : RowMatrix m I
  diag : ∀ i, entry i i=0
  sign : ∀ i j, i≠j → Sign (entry i j)
  skew : ∀ i j, entry i j= -entry j i
  row : ∀ i, ∑ j, entry i j=0
  gram : ∀ i k, ∑ j, entry i j*entry k j=(if i=k then (Fintype.card I : ZMod m) else 0)-1

def SkewCore.inner (P : SkewCore m I) : Rows m I (-1) where
  entry i j := P.entry i j + if i=j then 1 else 0
  sign i j := by
    by_cases h : i=j
    · subst j; simp [P.diag,Sign]
    · simpa [h] using P.sign i j h
  row i := by simp [Finset.sum_add_distrib,P.row]
  off i k ne := by
    have expand (j : I) :
        (P.entry i j+(if i=j then 1 else 0))*(P.entry k j+(if k=j then 1 else 0))=
          P.entry i j*P.entry k j + (if j=k then P.entry i k else 0) +
          (if j=i then P.entry k i else 0) := by
      by_cases a : i=j <;> by_cases b : k=j
      · exact (ne (a.trans b.symm)).elim
      · subst j; simp [ne,ne.symm] <;> ring
      · subst j; simp [ne,ne.symm] <;> ring
      · simp [a,b,Ne.symm a,Ne.symm b]
    simp only [expand,Finset.sum_add_distrib,P.gram,if_neg ne,zero_sub]
    simp [P.skew i k]

def SkewCore.block (P : SkewCore m I) {c : ZMod m} (B : Rows m J c) (i j : I×J) : ZMod m :=
  P.entry i.1 j.1 + if i.1=j.1 then B.entry i.2 j.2 else 0

private theorem block_dot (P : SkewCore m I) {c : ZMod m} (B : Rows m J c) (i k : I) (a b : J) :
    (∑ j, P.block B (i,a) j * P.block B (k,b) j) =
      ((Fintype.card J : ℕ) : ZMod m)*(∑ j,P.entry i j*P.entry k j)
      + (if i=k then ∑ j,B.entry a j*B.entry b j else 0) := by
  classical
  let t : ZMod m := ∑ j, B.entry a j*B.entry b j
  have expand (j : I) (u : J) : P.block B (i,a) (j,u) * P.block B (k,b) (j,u) =
      P.entry i j*P.entry k j +
      (if k=j then P.entry i k * B.entry b u else 0) +
      (if i=j then P.entry k i * B.entry a u else 0) +
      (if i=k ∧ i=j then B.entry a u * B.entry b u else 0) := by
    dsimp [SkewCore.block]
    by_cases hi : i=j <;> by_cases hk : k=j
    · subst j; subst k; simp; ring
    · subst j; simp [hk,Ne.symm hk]; ring
    · subst j; simp [hi,Ne.symm hi]; ring
    · simp [hi,hk]
  rw [Fintype.sum_prod_type]
  simp only [expand,Finset.sum_add_distrib]
  have term (j : I) : (∑ u : J,if i=k ∧ i=j then B.entry a u*B.entry b u else 0)=
      if i=j then (if i=k then t else 0) else 0 := by
    by_cases h : i=k <;> by_cases e : i=j <;> simp [h,e,t]
  simp only [term,Finset.sum_ite_irrel,Finset.sum_const_zero,←Finset.mul_sum,B.row,mul_one,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [Finset.mul_sum]
  simp only [mul_left_comm]
  dsimp [t]
  linear_combination P.skew i k

/-- If the product of the two orders is one modulo m, the two possible
off-diagonal correlations coincide. The target order is one plus the inner order. -/
def lexExtension (P : SkewCore m I) (B : Rows m J (-1)) [Nonempty I] [Nonempty J]
    (h : ((Fintype.card I * Fintype.card J : ℕ) : ZMod m)=1) :
    Extender m (I×J) (1+(Fintype.card J:ZMod m)) where
  entry := P.block B
  sign := by
    rintro ⟨i,a⟩ ⟨j,b⟩
    by_cases eq : i=j
    · subst j; simpa [SkewCore.block,P.diag] using B.sign a b
    · simpa [SkewCore.block,eq] using P.sign i j eq
  row := by
    rintro ⟨i,a⟩
    rw [Fintype.sum_prod_type]
    dsimp [SkewCore.block]
    have conditional (j : I) : (∑ b, if i=j then B.entry a b else 0)=if i=j then 1 else 0 := by
      by_cases e : i=j <;> simp [e,B.row]
    simp [Finset.sum_add_distrib,conditional,←Finset.mul_sum,P.row]
  off := by
    rintro ⟨i,a⟩ ⟨k,b⟩ ne
    rw [block_dot,P.gram]
    by_cases eq : i=k
    · subst k
      have nd : a≠b := fun e => ne (Prod.ext rfl e)
      rw [if_pos rfl,if_pos rfl,B.off _ _ nd]
      push_cast at h
      linear_combination h
    · rw [if_neg eq,if_neg eq]
      ring
  dim := by simpa using h
  pos := Fintype.card_pos

/-- Any orthogonal sign matrix can be squared in order to obtain constant
row sum equal to its original order. This works over an arbitrary modulus. -/
def squareRegular {H : RowMatrix m I} (g : Good H) (i j : I×I) : ZMod m :=
  H i.1 i.2*H i.1 j.2*H j.1 i.2*H j.1 j.2

end HadamardMod
