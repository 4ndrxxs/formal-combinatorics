import PencilPolynomialWeights
import PencilChainParity
import Mathlib.Tactic

/-! A linear nilpotent pencil has an explicitly weighted chain determinant.
A chain-length divisibility failure forces a residue prime of bounded degree. -/
noncomputable section
open Polynomial Matrix Finset
namespace PencilChain
open PencilWeight
variable {K k : Type*} [Field K] [Fintype k] [DecidableEq k]

theorem top_frame {s : ℕ} (A : Matrix (Fin s × k) (Fin s × k) K[X])
    (a : Matrix (Fin s × k) (Fin s × k) K) (h : ∀ i j, Top (A i j) 1 (a i j))
    (V : Matrix (Fin s × k) k K) :
    Top (frame s A (V.map C)).det (∑ j : Fin s × k, j.1.val) (frame s a V).det := by
  apply top_det
  intro i j
  have v (i l) : Top (V.map C i l) 0 (V i l) := by simp [PencilWeight.Top]
  simpa only [Nat.add_zero,frame,Matrix.of_apply] using
    (top_matrix_mul (A^j.1.val) (V.map C) (a^j.1.val) V j.1.val 0
      (top_matrix_pow A a h j.1.val) v i j.2)

theorem bad_prime_of_slope {s : ℕ} (length : s=2 ∨ s=4)
    (A : Matrix (Fin s × k) (Fin s × k) K[X])
    (a : Matrix (Fin s × k) (Fin s × k) K) (h : ∀ i j, Top (A i j) 1 (a i j))
    (nil : A^s=0) (nil₁ : a^s=0) (full : (a^(s-1)).rank = Fintype.card k)
    (bad : ¬s ∣ ∑ j : Fin s × k, j.1.val) :
    ∃ p : K[X], ∃ hp : Irreducible p, p.natDegree ≤ (∑ j : Fin s × k, j.1.val) ∧
      (let _ := Fact.mk hp; ((A.map (AdjoinRoot.mk p))^(s-1)).rank ≠ Fintype.card k) := by
  obtain ⟨V,good⟩ := exists_full_frame length a nil₁ full
  obtain ⟨le,coeff⟩ := top_frame A a h V
  have nzcoeff : (frame s A (V.map C)).det.coeff (∑ j : Fin s × k, j.1.val) ≠ 0 := coeff.trans_ne good
  have nz : (frame s A (V.map C)).det ≠ 0 := by
    intro eq
    simp only [eq,coeff_zero] at nzcoeff
    exact nzcoeff rfl
  have degree := natDegree_eq_of_le_of_coeff_ne_zero le nzcoeff
  obtain ⟨p,hp,dvd,lose⟩ := residue_rank_drop length A nil (V.map C) nz (degree ▸ bad)
  exact ⟨p,hp,(natDegree_le_of_dvd dvd nz).trans le,lose⟩

theorem square_zero_five_bad (A : Matrix (Fin 2 × Fin 5) (Fin 2 × Fin 5) K[X])
    (a : Matrix (Fin 2 × Fin 5) (Fin 2 × Fin 5) K)
    (h : ∀ i j, Top (A i j) 1 (a i j)) (nil : A^2=0) (nil₁ : a^2=0) (full : a.rank = 5) :
    ∃ p : K[X], ∃ hp : Irreducible p, p.natDegree ≤ 5 ∧
       (let _ := Fact.mk hp; (A.map (AdjoinRoot.mk p)).rank ≠ 5) := by
  have good : (a^(2-1)).rank = Fintype.card (Fin 5) := by simpa using full
  have total : (∑ j : Fin 2 × Fin 5, j.1.val) = 5 := by decide
  obtain ⟨p,hp,deg,drop⟩ := bad_prime_of_slope (Or.inl rfl) A a h nil nil₁ good
     (by rw [total]; decide)
  refine ⟨p,hp,total ▸ deg,?_⟩
  dsimp only at drop ⊢
  simpa using drop

#print axioms bad_prime_of_slope
#print axioms square_zero_five_bad
end PencilChain
