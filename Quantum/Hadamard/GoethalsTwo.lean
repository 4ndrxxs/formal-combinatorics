import Quantum.Hadamard.Goethals

/-! A pair of complementary sign sequences on a finite abelian group supplies
a sign matrix of twice the group order. -/
namespace HadamardMod
open Finset
variable {I : Type*} [Fintype I] [AddCommGroup I] {m : ℕ}

private theorem two_direct (a : Seq m I) (i j : I) :
    (∑ x,a (x-i)*a (x-j)) = cyclicCorr a a (i-j) := by
  have h := (Equiv.subRight i).sum_comp (fun x => a x*a (x+(i-j)))
  change (∑ x,a (x-i)*a (x-i+(i-j))) = _ at h
  have eq (x : I) : x-i+(i-j)=x-j := by abel
  simpa only [eq,cyclicCorr] using h

private theorem two_reversed (b : Seq m I) (i j : I) :
    (∑ x,b (-i-x)*b (-j-x)) = cyclicCorr b b (i-j) := by
  have h := (Equiv.subLeft (-i)).sum_comp (fun x => b x*b (x+(i-j)))
  change (∑ x,b (-i-x)*b (-i-x+(i-j))) = _ at h
  have eq (x : I) : -i-x+(i-j)= -j-x := by abel
  simpa only [eq,cyclicCorr] using h

private theorem two_swap (a b : Seq m I) (i j : I) :
    (∑ x,a (x-i)*b (-j-x)) = ∑ x,b (-i-x)*a (x-j) := by
  have h := Equiv.sum_comp (Equiv.addRight (i-j)) (fun x => a (x-i)*b (-j-x))
  change (∑ x,a (x+(i-j)-i)*b (-j-(x+(i-j)))) = _ at h
  have e (x:I) : x+(i-j)-i=x-j := by abel
  have f (x:I) : -j-(x+(i-j))= -i-x := by abel
  simpa only [e,f,mul_comm] using h.symm

theorem two_circulants (a b : Seq m I) (sa : ∀ x,Sign (a x)) (sb : ∀ x,Sign (b x))
    (hc : ∀ s:I,s≠0 → cyclicCorr a a s+cyclicCorr b b s=0) :
    AtOrder m (2*Fintype.card I) := by
  let H : RowMatrix m (I⊕I)
    | .inl i,.inl j => a (j-i)
    | .inl i,.inr j => b (-i-j)
    | .inr i,.inl j => -b (-i-j)
    | .inr i,.inr j => a (j-i)
  apply of_card (A:=H) _ (by simp [two_mul])
  constructor
  · intro i j
    rcases i with i|i <;> rcases j with j|j
    · exact sa _
    · exact sb _
    · rcases sb (-i-j) with h|h <;> simp [H,Sign,h]
    · exact sa _
  · intro i j ne
    rw [Fintype.sum_sum_type]
    rcases i with i|i <;> rcases j with j|j
    · have d : i≠j := fun h => ne (congrArg Sum.inl h)
      simpa [H,two_direct,two_reversed] using hc (i-j) (sub_ne_zero.mpr d)
    · simp [H,two_swap]
    · simp [H,two_swap]
    · have d : i≠j := fun h => ne (congrArg Sum.inr h)
      simpa [H,two_direct,two_reversed,add_comm] using hc (i-j) (sub_ne_zero.mpr d)

#print axioms two_circulants
end HadamardMod

