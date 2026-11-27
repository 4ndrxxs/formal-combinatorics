import Quantum.Hadamard.ConferenceBitBound

/-! Four-fifths determinant certificates for complete matrices supplied as
binary rows. The finite hypotheses use only integer and natural arithmetic. -/
noncomputable section
open Matrix
open Hadamard.DeterminantRatio

namespace Hadamard.BitTrace

/-- Replace each bit by its sign, then remove the positive diagonal. -/
def realWordBlock {n : ℕ} (w : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (wordMatrix w-1).map (Int.castRingHom ℝ)

theorem word_conference_square {n : ℕ} (w : Fin n → ℕ)
    (sym : (wordMatrix w).IsSymm) (diag : ∀ i : Fin n, sign (w i) i.val=1)
    (pair : ∀ i j : Fin n, i≠j → correlation n (w i) (w j)=2*sign (w i) j.val) :
    (wordMatrix w-1)*(wordMatrix w-1)=((n:ℤ)-1) • (1 : Matrix _ _ ℤ) := by
  let M := wordMatrix w
  have expand : (M-1)*(M-1)=M^2-M-M+1 := by noncomm_ring
  rw [show (wordMatrix w-1)*(wordMatrix w-1)=M^2-M-M+1 from expand]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.one_apply,Matrix.smul_apply,
    smul_eq_mul,M,square_entry w sym]
  by_cases h : i=j
  · subst j
    simp [correlation_self,wordMatrix,diag]
  · simp [h,pair i j h,wordMatrix]
    ring

private theorem real_word_properties {n : ℕ} (w : Fin n → ℕ)
    (sym : (wordMatrix w).IsSymm) (diag : ∀ i : Fin n, sign (w i) i.val=1)
    (pair : ∀ i j : Fin n, i≠j → correlation n (w i) (w j)=2*sign (w i) j.val) :
    (realWordBlock w).IsHermitian ∧ (realWordBlock w)*(realWordBlock w)=
      ((n:ℝ)-1) • (1 : Matrix _ _ ℝ) ∧
    (∀ i, realWordBlock w i i=0) ∧ (∀ i j, i≠j → realWordBlock w i j^2=1) := by
  have hs : (wordMatrix w-1).IsSymm := sym.sub Matrix.isSymm_one
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    change ((wordMatrix w-1) j i:ℝ)=((wordMatrix w-1) i j:ℝ)
    exact_mod_cast hs.apply i j
  · unfold realWordBlock
    rw [←Matrix.map_mul,word_conference_square w sym diag pair]
    ext i j
    simp only [Matrix.map_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,map_mul,map_sub,map_natCast,map_one]
    by_cases h : i=j <;> simp [h]
  · intro i
    simp [realWordBlock,wordMatrix,Matrix.sub_apply,diag]
  · intro i j h
    simp only [realWordBlock, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
      ite_eq_right h, sub_zero, wordMatrix, sign]
    cases (w i).testBit j.val <;> norm_num

/-- Reorder the full conference matrix by listing positive indices first. -/
def orderedWordBlock {n v : ℕ} (w : Fin n → ℕ) (e : Fin v ⊕ Fin v ≃ Fin n) :=
  (realWordBlock w).submatrix e e

/-- A lower bound on the determinant of the explicit completed matrix. Both
the conference identity and the identification of its principal block are
discharged by arithmetic on the supplied rows and permutations. -/
theorem explicit_determinant {n : ℕ} (k : ℕ) (full : Fin n → ℕ)
    (w : Fin (k+1) → ℕ) (e : (Fin (k+1) ⊕ Fin (k+1)) ≃ Fin n)
    (order : n=2*(k+1)) (size : 29≤2*(k:ℝ)+1)
    (sym : (wordMatrix full).IsSymm) (diag : ∀ i : Fin n, sign (full i) i.val=1)
    (pair : ∀ i j : Fin n, i≠j → correlation n (full i) (full j)=2*sign (full i) j.val)
    (rows : ∀ i j : Fin (k+1), sign (full (e (Sum.inl i))) (e (Sum.inl j)).val=sign (w i) j.val)
    (margin : let v : ℤ := (k:ℤ)+1
      0≤87*v^3+375*v*(4*v-3)+1000*((wordMatrix w-1)^3).trace-
        1110*(2*v-1)*(v-1)) :
    (4/5:ℝ)*ewBound k ≤ |(orderedWordBlock full e+diagonal completionSign).det| := by
  obtain ⟨herm,square,zero,off⟩ := real_word_properties full sym diag pair
  have nr : (n:ℝ)-1=2*(k:ℝ)+1 := by rw [order]; push_cast; ring
  have sq : (orderedWordBlock full e)*(orderedWordBlock full e)=(2*(k:ℝ)+1) • 1 := by
    unfold orderedWordBlock
    rw [submatrix_mul_equiv,square]
    change ((n:ℝ)-1) • ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix e e)=_
    rw [submatrix_one_equiv,nr]
  apply four_fifths_of_word_block k w size (herm.submatrix e) sq (fun i ↦ zero (e i))
    (fun i j h ↦ off _ _ (e.injective.ne h)) _ margin
  ext i j
  simp only [realWordBlock,Matrix.submatrix_apply,Matrix.map_apply,
    Matrix.sub_apply,Matrix.one_apply,wordMatrix,Equiv.apply_eq_iff_eq,Sum.inl.injEq,rows]

#print axioms word_conference_square
#print axioms explicit_determinant

end Hadamard.BitTrace
