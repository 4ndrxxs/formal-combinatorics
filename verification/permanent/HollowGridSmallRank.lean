import HollowGridFactor

/-! Small ranks of separately symmetric hollow grid forms over any field. -/
noncomputable section
open Matrix
namespace HollowGrid
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]
omit [Fintype I] [Fintype J] in
theorem PairSymmetric.scale {H : Matrix (I × J) (I × J) K} (P : PairSymmetric H) (x : K) :
    PairSymmetric (x • H) := by
  constructor
  · intro r i j
    simp [Matrix.smul_apply,P.rows]
  · intro i r s
    simp [Matrix.smul_apply,P.cols]
  · intro r s i j
    simp [Matrix.smul_apply,P.swapRow r s i j]
  · intro r s i j
    simp [Matrix.smul_apply,P.swapCol r s i j]

/-- A nonzero grid form of rank at most five has rank four and is the
product of two symmetrized rank-one factors. -/
theorem small_factorization (H : Matrix (I × J) (I × J) K) (P : PairSymmetric H)
    (hn : H ≠ 0) (hr : H.rank ≤ 5) :
    H.rank=4 ∧ ∃ (R S : I → K) (C D : J → K), ∀ r s i j,
      H (r,i) (s,j) = (R r*S s+S r*R s)*(C i*D j+D i*C j) := by
  classical
  obtain ⟨⟨a,p⟩,⟨b,q⟩,nz⟩ : ∃ u v, H u v ≠ 0 := by
    by_contra! h
    exact hn (Matrix.ext fun u v ↦ h u v)
  let x := H (a,p) (b,q)
  have hx : x≠0 := nz
  let T := x⁻¹ • H
  have rt : T.rank = H.rank :=
    Matrix.rank_smul_of_mem_nonZeroDivisors H (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero hx))
  have one : T (a,p) (b,q)=1 := by
    change x⁻¹*x=1
    exact inv_mul_cancel₀ hx
  obtain ⟨four,R,S,C,D,h⟩ := normalized_factorization T (P.scale x⁻¹)
    (rt.trans_le hr) a b p q one
  refine ⟨rt.symm.trans four,fun r ↦ x*R r,S,C,D,?_⟩
  intro r s i j
  have hh := h r s i j
  change x⁻¹*H (r,i) (s,j)=_ at hh
  calc H (r,i) (s,j) = x*(x⁻¹*H (r,i) (s,j)) := by simp [hx]
       _ = _ := by rw [hh]; ring

theorem rank_gap (H : Matrix (I × J) (I × J) K) (P : PairSymmetric H) :
    H.rank=0 ∨ H.rank=4 ∨ 6≤H.rank := by
  by_cases e : H=0
  · exact Or.inl (by rw [e,Matrix.rank_zero])
  by_cases h : H.rank≤5
  · exact Or.inr (Or.inl (small_factorization H P e h).1)
  · omega

#print axioms small_factorization
#print axioms rank_gap
end HollowGrid
