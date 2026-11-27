import PencilFourFlags

/-! Passage from an arbitrary full slope to the four-layer shift. -/
noncomputable section
open Matrix Finset Polynomial
namespace PencilLayers
variable {K : Type*} [Field K]

private theorem times_shift (F : Matrix (Layer 4) (Layer 4) K) (i : Layer 4) (j : Fin 4) (k : Fin 5) :
    (F*shift K 4) i (j,k) = ∑ q : Fin 4, if q.val=j.val+1 then F i (q,k) else 0 := by
  rw [Matrix.mul_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  by_cases eq : q.val=j.val+1 <;> simp [shift,eq]

theorem frame_shift (a : Matrix (Layer 4) (Layer 4) K) (nil : a^4=0)
    (V : Matrix (Layer 4) (Fin 5) K) :
    a*PencilChain.frame 4 a V = PencilChain.frame 4 a V * shift K 4 := by
  let F := PencilChain.frame 4 a V
  have layer (j : Fin 4) : PencilChain.columns (a*F) j = a^(j.val+1)*V := by
    rw [PencilChain.columns_mul]
    change a*(a^j.val*V) = a^(j.val+1)*V
    rw [←Matrix.mul_assoc,←pow_succ']
  ext i j
  obtain ⟨j,k⟩ := j
  change PencilChain.columns (a*F) j i k = _
  rw [layer,times_shift]
  fin_cases j <;> simp [Fin.sum_univ_succ,PencilChain.frame,nil]

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem conjugate_pow (A T U : Matrix n n R) (tu : T*U=1) (ut : U*T=1) (r : ℕ) :
    (U*A*T)^r=U*(A^r)*T := by
  induction r with
  | zero => simp [ut]
  | succ r ih =>
    rw [pow_succ,ih,pow_succ]
    calc U*A^r*T*(U*A*T) = U*A^r*(T*U)*A*T := by simp only [Matrix.mul_assoc]
         _ = _ := by rw [tu,Matrix.mul_one,Matrix.mul_assoc U]

theorem conjugate_rank (A T U : Matrix n n K) (tu : T*U=1) :
    (U*A*T).rank=A.rank := by
  apply le_antisymm ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))
  have eq : T*(U*A*T)*U=A := by
    calc T*(U*A*T)*U=(T*U)*A*(T*U) := by simp only [Matrix.mul_assoc]
         _ = A := by rw [tu,Matrix.one_mul,Matrix.mul_one]
  conv_lhs => rw [←eq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

omit [DecidableEq n] in
theorem constant_conjugate_top (A : Matrix n n K[X]) (a T U : Matrix n n K)
    (h : ∀ i j, PencilWeight.Top (A i j) 1 (a i j)) :
    ∀ i j, PencilWeight.Top ((U.map C*A*T.map C) i j) 1 ((U*a*T) i j) := by
  have c (M : Matrix n n K) (i j : n) : PencilWeight.Top (M.map C i j) 0 (M i j) := by
    simp [PencilWeight.Top]
  have left := PencilWeight.top_matrix_mul (U.map C) A U a 0 1 (c U) h
  simpa only [Nat.zero_add,Nat.add_zero] using
    PencilWeight.top_matrix_mul (U.map C*A) (T.map C) (U*a) T (0+1) 0 left (c T)

#print axioms frame_shift
#print axioms constant_conjugate_top
end PencilLayers
