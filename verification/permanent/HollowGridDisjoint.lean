import HollowGridSmallRank

/-! Over a field of characteristic different from two, the factors of a
nonzero grid form of rank at most five have disjoint coordinate supports.
The explicit product criterion is also sufficient for rank four. -/
noncomputable section
open Matrix
namespace HollowGrid
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

theorem disjoint_factorization (H : Matrix (I×J) (I×J) K) (P : PairSymmetric H)
    (two : (2:K)≠0) (hn : H≠0) (hr : H.rank≤5) :
    ∃ (R S : I → K) (C D : J → K), (∀ r, R r*S r=0) ∧ (∀ i, C i*D i=0) ∧
    ∀ r s i j, H (r,i) (s,j)=(R r*S s+S r*R s)*(C i*D j+D i*C j) := by
  obtain ⟨_,R,S,C,D,h⟩ := small_factorization H P hn hr
  obtain ⟨⟨a,p⟩,⟨b,q⟩,nz⟩ : ∃ u v, H u v≠0 := by
    by_contra! v
    exact hn (Matrix.ext fun u w ↦ v u w)
  rw [h] at nz
  have row : R a*S b+S a*R b≠0 := left_ne_zero_of_mul nz
  have col : C p*D q+D p*C q≠0 := right_ne_zero_of_mul nz
  refine ⟨R,S,C,D,?_,?_,h⟩
  · intro r
    have v := h r r p q
    rw [P.rows] at v
    have e := (mul_eq_zero.mp v.symm).resolve_right col
    have t : 2*(R r*S r)=0 := by linear_combination e
    exact (mul_eq_zero.mp t).resolve_left two
  · intro i
    have v := h a b i i
    rw [P.cols] at v
    have e := (mul_eq_zero.mp v.symm).resolve_left row
    have t : 2*(C i*D i)=0 := by linear_combination e
    exact (mul_eq_zero.mp t).resolve_left two

theorem rank_four_iff (H : Matrix (I×J) (I×J) K) (P : PairSymmetric H) (hn : H≠0) :
    H.rank=4 ↔ ∃ (R S : I → K) (C D : J → K), ∀ r s i j,
      H (r,i) (s,j)=(R r*S s+S r*R s)*(C i*D j+D i*C j) := by
  constructor
  · intro h
    exact (small_factorization H P hn (by omega)).2
  · rintro ⟨R,S,C,D,h⟩
    let A : Matrix (I×J) (Fin 4) K := Matrix.of fun u ↦
      ![R u.1*C u.2,R u.1*D u.2,S u.1*C u.2,S u.1*D u.2]
    let B : Matrix (Fin 4) (I×J) K := Matrix.of fun k v ↦
      ![S v.1*D v.2,S v.1*C v.2,R v.1*D v.2,R v.1*C v.2] k
    have split : H=A*B := by
      ext ⟨r,i⟩ ⟨s,j⟩
      rw [h]
      simp [A,B,Matrix.mul_apply,Fin.sum_univ_succ]
      ring
    have four : H.rank≤4 := by
      rw [split]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
    exact (small_factorization H P hn (by omega)).1

#print axioms disjoint_factorization
#print axioms rank_four_iff
end HollowGrid
